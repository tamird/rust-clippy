use clippy_utils::macros::{FormatArgsStorage, StoredFormatArgs};
use clippy_utils::source::{SpanExt as _, walk_span_to_context};
use rustc_ast::visit::{self, Visitor};
use rustc_ast::{Crate, Expr, ExprKind, FormatArgs, FormatArgumentKind};
use rustc_data_structures::fx::FxHashMap;
use rustc_lexer::{FrontmatterAllowed, TokenKind, tokenize};
use rustc_lint::{EarlyContext, EarlyLintPass, LintContext as _, impl_lint_pass};
use rustc_span::source_map::SourceMap;
use rustc_span::{BytePos, Pos as _, Span, SpanData};
use std::iter::Peekable;
use std::mem;
use std::ops::ControlFlow;

/// Populates [`FormatArgsStorage`] with AST [`FormatArgs`] nodes
pub struct FormatArgsCollector {
    format_args: FxHashMap<Span, StoredFormatArgs>,
    parent_spans: Vec<SpanData>,
    storage: FormatArgsStorage,
}

impl FormatArgsCollector {
    pub fn new(storage: FormatArgsStorage) -> Self {
        Self {
            format_args: FxHashMap::default(),
            parent_spans: Vec::new(),
            storage,
        }
    }
}

impl_lint_pass!(FormatArgsCollector => []);

impl EarlyLintPass for FormatArgsCollector {
    fn check_expr(&mut self, cx: &EarlyContext<'_>, expr: &Expr) {
        if let ExprKind::FormatArgs(args) = &expr.kind
            && let Some(args) = self.collect_format_args(cx.sess().source_map(), expr.span, args)
        {
            self.format_args.insert(expr.span.with_parent(None), args);
        }
    }

    fn check_crate_post(&mut self, _: &EarlyContext<'_>, _: &Crate) {
        self.storage.set(mem::take(&mut self.format_args));
    }
}

impl FormatArgsCollector {
    /// Detects if the format string has its span set by a proc macro to something
    /// inside a macro callsite, e.g.
    ///
    /// ```ignore
    /// println!(some_proc_macro!("input {}"), a);
    /// ```
    ///
    /// Where `some_proc_macro` expands to
    ///
    /// ```ignore
    /// println!("output {}", a);
    /// ```
    ///
    /// But with the span of `"output {}"` set to the macro input
    ///
    /// ```ignore
    /// println!(some_proc_macro!("input {}"), a);
    /// //                        ^^^^^^^^^^
    /// ```
    fn collect_format_args(&mut self, sm: &SourceMap, fmt_sp: Span, args: &FormatArgs) -> Option<StoredFormatArgs> {
        let mut fmt_sp = fmt_sp.data();

        // Find the first macro call that contains the format string.
        let arg_sp = if let Some(arg_sp) = walk_span_to_context(args.span, fmt_sp.ctxt) {
            arg_sp.data()
        } else {
            // Try to find a common parent for the format call and the format string.
            self.parent_spans.clear();
            // `fmt_sp.ctxt` isn't a parent of the format string so don't add it to the
            // search. The first iteration will always run since it can't be the root.
            while !fmt_sp.ctxt.is_root() {
                fmt_sp = fmt_sp.ctxt.outer_expn_data().call_site.data();
                self.parent_spans.push(fmt_sp);
            }
            let mut arg_sp = args.span.data();
            // Note: A parent span will always eventually be found since the root context
            // is an ancestor of all contexts.
            loop {
                match self.parent_spans.iter().find(|s| s.ctxt == arg_sp.ctxt) {
                    Some(call_sp) if call_sp.lo <= arg_sp.lo && arg_sp.hi <= call_sp.hi => {
                        fmt_sp = *call_sp;
                        break arg_sp;
                    },
                    // If the string isn't within the call span we some macro stuff we can't
                    // easily interpret.
                    Some(_) => return None,
                    None => arg_sp = arg_sp.ctxt.outer_expn_data().call_site.data(),
                }
            }
        };
        if fmt_sp.ctxt.in_external_macro(sm) {
            return None;
        }
        let src = arg_sp.get_source_range(sm)?;
        let src_text = src.sf.src.as_ref().map(|x| &***x)?;

        // Check the spans between the format string and the arguments and between each argument.
        let mut collected = args.clone();
        let explicit = collected.arguments.explicit_args().len();
        let mut recovered = false;
        let mut start = src.range.end;
        for arg in &mut collected.arguments.all_args_mut()[..explicit] {
            let start_pos = src.sf.start_pos + BytePos::from_usize(start);
            let expr_span = walk_span_to_context(arg.expr.span, fmt_sp.ctxt)
                .filter(|span| span.lo() >= start_pos)
                .or_else(|| {
                    recovered = true;
                    find_source_expr(
                        &arg.expr,
                        Span::new(start_pos, src.sf.end_position(), fmt_sp.ctxt, None),
                    )
                });
            let Some(expr_span) = expr_span else {
                if matches!(arg.kind, FormatArgumentKind::Named(_)) && args.span.contains(arg.original_span) {
                    continue;
                }
                return None;
            };
            let expr_start = (expr_span.lo() - src.sf.start_pos).to_usize();
            let expr_end = (expr_span.hi() - src.sf.start_pos).to_usize();
            let mut tks = source_tokens(src_text.get(start..expr_end)?).peekable();
            if !matches!(tks.next(), Some((_, TokenKind::Comma))) {
                return None;
            }
            let (arg_offset, value_offset, _) = argument_value_token(&mut tks)?;
            if expr_start != start + arg_offset && expr_start != start + value_offset {
                return None;
            }
            if !matches!(
                source_tokens(src_text.get(expr_end..)?).next(),
                Some((
                    _,
                    TokenKind::Comma | TokenKind::CloseParen | TokenKind::CloseBracket | TokenKind::CloseBrace
                ))
            ) {
                return None;
            }
            let arg_start = src.sf.start_pos + BytePos::from_usize(start + arg_offset);
            arg.original_span = expr_span.with_lo(arg_start);
            start = expr_end;
        }
        Some(if recovered {
            StoredFormatArgs::Recovered(collected)
        } else {
            StoredFormatArgs::Direct(collected)
        })
    }
}

pub(crate) fn argument_value_token(
    tokens: &mut Peekable<impl Iterator<Item = (usize, TokenKind)>>,
) -> Option<(usize, usize, TokenKind)> {
    let first = tokens.next()?;
    let value = if first.1 == TokenKind::Ident && tokens.next_if(|(_, kind)| *kind == TokenKind::Eq).is_some() {
        tokens.next()?
    } else {
        first
    };
    Some((first.0, value.0, value.1))
}

pub(crate) fn source_tokens(src: &str) -> impl Iterator<Item = (usize, TokenKind)> {
    let mut offset = 0;
    tokenize(src, FrontmatterAllowed::No).filter_map(move |token| {
        let start = offset;
        offset += token.len as usize;
        (!matches!(
            token.kind,
            TokenKind::LineComment { doc_style: None }
                | TokenKind::BlockComment {
                    doc_style: None,
                    terminated: true
                }
                | TokenKind::Whitespace
        ))
        .then_some((start, token.kind))
    })
}

fn find_source_expr(expr: &Expr, source: Span) -> Option<Span> {
    struct SourceExpr {
        source: Span,
        found: Option<Span>,
    }

    impl<'a> Visitor<'a> for SourceExpr {
        type Result = ControlFlow<()>;

        fn visit_expr(&mut self, expr: &'a Expr) -> Self::Result {
            if self.source.ctxt() == expr.span.ctxt() && self.source.contains(expr.span) {
                if let Some(found) = self.found
                    && found != expr.span
                {
                    return ControlFlow::Break(());
                }
                self.found = Some(expr.span);
                ControlFlow::Continue(())
            } else {
                visit::walk_expr(self, expr)
            }
        }
    }

    let mut visitor = SourceExpr { source, found: None };
    visitor.visit_expr(expr).continue_value()?;
    visitor.found
}
