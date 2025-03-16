use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Error, Diagnostic, Debug, Clone, PartialEq)]
#[error("syntax error")]
pub enum SyntaxError {
    #[error("unexpected token")]
    #[diagnostic(code(meta_c::unexpected_token))]
    UnexpectedToken {
        #[label]
        at: SourceSpan,
    },

    #[error("mismatched closing delimiter")]
    #[diagnostic(code(meta_c::mismatched_closing_delimiter))]
    MismatchedClosingDelimiter {
        #[label]
        at: SourceSpan,
    },
}
