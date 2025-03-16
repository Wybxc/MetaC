use std::{fmt::Display, ops::Range};

use ecow::{EcoString, EcoVec};
use elegance::{Printer, Render};
use logos::{Lexer, Logos};

use crate::error::SyntaxError;

pub fn lex(source: &str) -> Result<TokenStream, SyntaxError> {
    let mut lexer = MetaLexer::new();
    for (token, span) in TokenUnit::lexer(source).spanned() {
        lexer.lex(
            token.map_err(|_| SyntaxError::UnexpectedToken {
                at: span.clone().into(),
            })?,
            span,
        )?;
    }
    Ok(lexer.finish())
}

struct MetaLexer {
    stream: TokenStream,
    delimiters: Vec<(Delimiter, TokenStream)>,
    last_is_punct: bool,
}

impl MetaLexer {
    pub fn new() -> MetaLexer {
        MetaLexer {
            stream: TokenStream::new(),
            delimiters: Vec::new(),
            last_is_punct: false,
        }
    }

    pub fn finish(mut self) -> TokenStream {
        while let Some((delimiter, outer)) = self.delimiters.pop() {
            let inner = std::mem::replace(&mut self.stream, outer);
            self.stream.push(TokenTree::Group(Group {
                delimiter,
                stream: inner,
                terminated: false,
            }));
        }
        self.stream
    }

    pub fn lex(&mut self, token: TokenUnit, span: Range<usize>) -> Result<(), SyntaxError> {
        self.last_is_punct = false;

        match token {
            TokenUnit::ParenOpen => self.delimiter_open(Delimiter::Parenthesis),
            TokenUnit::BraceOpen => self.delimiter_open(Delimiter::Brace),
            TokenUnit::BracketOpen => self.delimiter_open(Delimiter::Bracket),
            TokenUnit::DoubleBracketOpen => self.delimiter_open(Delimiter::DoubleBracket),

            TokenUnit::ParenClose => self.delimiter_close(Delimiter::Parenthesis, span)?,
            TokenUnit::BraceClose => self.delimiter_close(Delimiter::Brace, span)?,
            TokenUnit::BracketClose => self.delimiter_close(Delimiter::Bracket, span)?,
            TokenUnit::DoubleBracketClose => {
                self.delimiter_close(Delimiter::DoubleBracket, span)?
            }

            TokenUnit::Punct(punct) => {
                if let Some(TokenTree::Punct(last_punct)) = self.stream.inner.last() {
                    if last_punct.spacing == Spacing::Alone && self.last_is_punct {
                        let Some(TokenTree::Punct(last_punct)) =
                            self.stream.inner.make_mut().last_mut()
                        else {
                            unreachable!()
                        };
                        last_punct.spacing = Spacing::Joint;
                    }
                }
                self.stream.push(TokenTree::Punct(Punct {
                    ch: punct,
                    spacing: if self.last_is_punct {
                        Spacing::Joint
                    } else {
                        Spacing::Alone
                    },
                }));
                self.last_is_punct = true;
            }

            TokenUnit::Ident(ident) => self.stream.push(TokenTree::Ident(Ident { sym: ident })),

            TokenUnit::Integer((lit, base, suffix)) => {
                self.stream.push(TokenTree::Literal(LiteralToken {
                    kind: LiteralKind::Int { base, suffix },
                    repr: lit,
                }))
            }
            TokenUnit::Float((lit, base, suffix)) => {
                self.stream.push(TokenTree::Literal(LiteralToken {
                    kind: LiteralKind::Float { base, suffix },
                    repr: lit,
                }))
            }
            TokenUnit::Char((lit, prefix, terminated)) => {
                self.stream.push(TokenTree::Literal(LiteralToken {
                    kind: LiteralKind::Char { prefix, terminated },
                    repr: lit,
                }))
            }
            TokenUnit::Str((lit, prefix, terminated)) => {
                self.stream.push(TokenTree::Literal(LiteralToken {
                    kind: LiteralKind::Str { prefix, terminated },
                    repr: lit,
                }))
            }
            TokenUnit::Bool((lit, value)) => self.stream.push(TokenTree::Literal(LiteralToken {
                kind: LiteralKind::Boolean { value },
                repr: lit,
            })),
            TokenUnit::Nullptr => self.stream.push(TokenTree::Literal(LiteralToken {
                kind: LiteralKind::Nullptr,
                repr: EcoString::from("nullptr"),
            })),

            TokenUnit::Whitespace => {}
            TokenUnit::Comment => {}
        }

        Ok(())
    }

    fn delimiter_open(&mut self, delimiter: Delimiter) {
        self.delimiters
            .push((delimiter, std::mem::take(&mut self.stream)));
    }

    fn delimiter_close(
        &mut self,
        delimiter: Delimiter,
        span: Range<usize>,
    ) -> Result<(), SyntaxError> {
        let Some((inner_delimiter, outer)) = self.delimiters.pop() else {
            return Err(SyntaxError::MismatchedClosingDelimiter { at: span.into() });
        };
        if inner_delimiter != delimiter {
            return Err(SyntaxError::MismatchedClosingDelimiter { at: span.into() });
        }
        let inner = std::mem::replace(&mut self.stream, outer);
        self.stream.push(TokenTree::Group(Group {
            delimiter: inner_delimiter,
            stream: inner,
            terminated: true,
        }));
        Ok(())
    }
}

/// A single token or a delimited sequence of token trees (e.g. `[1, (), ..]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenTree {
    /// A token stream surrounded by bracket delimiters.
    Group(Group),
    /// An identifier.
    Ident(Ident),
    /// A single punctuation character (`+`, `,`, `$`, etc.).
    Punct(Punct),
    /// A literal character (`'a'`), string (`"hello"`), number (`2.3`), etc.
    Literal(LiteralToken),
}

impl TokenTree {
    pub fn pretty<'a, R: Render>(
        &'a self,
        pp: &mut Printer<'a, R, EcoString>,
    ) -> Result<(), R::Error> {
        match self {
            TokenTree::Group(group) => group.pretty(pp),
            TokenTree::Ident(ident) => ident.pretty(pp),
            TokenTree::Punct(punct) => punct.pretty(pp),
            TokenTree::Literal(lit) => lit.pretty(pp),
        }
    }
}

/// A delimited token stream.
///
/// A `Group` internally contains a `TokenStream` which is surrounded by
/// `Delimiter`s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub delimiter: Delimiter,
    pub stream: TokenStream,
    pub terminated: bool,
    // pub span: Span,
}

impl Group {
    pub fn pretty<'a, R: Render>(
        &'a self,
        pp: &mut Printer<'a, R, EcoString>,
    ) -> Result<(), R::Error> {
        pp.text(match self.delimiter {
            Delimiter::Parenthesis => "(",
            Delimiter::Brace => "{",
            Delimiter::Bracket => "[",
            Delimiter::DoubleBracket => "[[",
        })?;
        pp.cgroup(2, |pp| {
            for tree in &self.stream.inner {
                match self.delimiter {
                    Delimiter::Brace => pp.space()?,
                    _ => pp.zero_break()?,
                }
                tree.pretty(pp)?;
            }
            match self.delimiter {
                Delimiter::Brace => pp.scan_break(1, -2)?,
                _ => pp.scan_break(0, -2)?,
            }
            Ok(())
        })?;
        if self.terminated {
            pp.text(match self.delimiter {
                Delimiter::Parenthesis => ")",
                Delimiter::Brace => "}",
                Delimiter::Bracket => "]",
                Delimiter::DoubleBracket => "]]",
            })?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    sym: EcoString,
}

impl Ident {
    pub fn pretty<'a, R: Render>(
        &'a self,
        pp: &mut Printer<'a, R, EcoString>,
    ) -> Result<(), R::Error> {
        pp.text(self.sym.as_str())
    }
}

/// A `Punct` is a single punctuation character like `+`, `-` or `#`.
///
/// Multicharacter operators like `+=` are represented as two instances of
/// `Punct` with different forms of `Spacing` returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Punct {
    pub ch: char,
    pub spacing: Spacing,
    // pub span: Span,
}

impl Punct {
    pub fn pretty<R: Render>(&self, pp: &mut Printer<'_, R, EcoString>) -> Result<(), R::Error> {
        pp.text_owned(self.ch)
    }
}

/// Whether a `Punct` is followed immediately by another `Punct` or followed by
/// another token or whitespace.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Spacing {
    /// E.g. `+` is `Alone` in `+ =`, `+ident` or `+()`.
    Alone,
    /// E.g. `+` is `Joint` in `+=` or `'` is `Joint` in `'#`.
    ///
    /// Additionally, single quote `'` can join with identifiers to form
    /// lifetimes `'ident`.
    Joint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralToken {
    kind: LiteralKind,
    repr: EcoString,
    // span: Span,
}

impl LiteralToken {
    pub fn pretty<'a, R: Render>(
        &'a self,
        pp: &mut Printer<'a, R, EcoString>,
    ) -> Result<(), R::Error> {
        self.kind.pretty_prefix(pp)?;
        pp.text(&self.repr)?;
        self.kind.pretty_suffix(pp)
    }
}

/// The possible forms a literal can be in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralKind {
    /// `true` or `false`.
    Boolean { value: bool },
    /// `nullptr`
    Nullptr,
    /// `12_u8`, `0o100`, `0b120i99`, `1f32`.
    Int { base: Base, suffix: IntSuffix },
    /// `12.34f32`, `1e3`, but not `1f32`.
    Float {
        base: FloatBase,
        suffix: FloatSuffix,
    },
    /// `'a'`, `'\\'`, `'''`, `';`
    Char { prefix: StrPrefix, terminated: bool },
    /// `"abc"`, `"abc`
    Str { prefix: StrPrefix, terminated: bool },
}

impl LiteralKind {
    pub fn pretty_prefix<R: Render>(
        &self,
        pp: &mut Printer<'_, R, EcoString>,
    ) -> Result<(), R::Error> {
        match self {
            LiteralKind::Char { prefix, .. } => match prefix {
                StrPrefix::None => pp.text("'")?,
                StrPrefix::Utf8 => pp.text("u8'")?,
                StrPrefix::Utf16 => pp.text("u'")?,
                StrPrefix::Utf32 => pp.text("U'")?,
                StrPrefix::Wide => pp.text("L'")?,
            },
            LiteralKind::Str { prefix, .. } => match prefix {
                StrPrefix::None => pp.text("\"")?,
                StrPrefix::Utf8 => pp.text("u8\"")?,
                StrPrefix::Utf16 => pp.text("u\"")?,
                StrPrefix::Utf32 => pp.text("U\"")?,
                StrPrefix::Wide => pp.text("L\"")?,
            },
            _ => {}
        }
        Ok(())
    }

    pub fn pretty_suffix<R: Render>(
        &self,
        pp: &mut Printer<'_, R, EcoString>,
    ) -> Result<(), R::Error> {
        match self {
            LiteralKind::Int { suffix, .. } => {
                if suffix.unsigned {
                    pp.text("u")?;
                }
                match suffix.long {
                    Some(IntLong::Long) => pp.text("l")?,
                    Some(IntLong::LongLong) => pp.text("ll")?,
                    Some(IntLong::BitPrecise) => pp.text("wb")?,
                    None => {}
                }
            }
            LiteralKind::Float { suffix, .. } => match suffix.long {
                Some(FloatLong::Float) => pp.text("f")?,
                Some(FloatLong::LongDouble) => pp.text("l")?,
                None => {}
            },
            LiteralKind::Char { .. } => pp.text("'")?,
            LiteralKind::Str { .. } => pp.text("\"")?,
            _ => {}
        }
        Ok(())
    }
}

/// Describes how a sequence of token trees is delimited.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
    /// `[[ ... ]]`
    DoubleBracket,
}

/// A `TokenStream` is an abstract sequence of tokens, organized into [`TokenTree`]s.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TokenStream {
    inner: EcoVec<TokenTree>,
}

impl TokenStream {
    pub fn new() -> TokenStream {
        TokenStream {
            inner: EcoVec::new(),
        }
    }

    pub fn push(&mut self, tree: TokenTree) {
        self.inner.push(tree);
    }

    pub fn pretty<'a, R: Render>(
        &'a self,
        pp: &mut Printer<'a, R, EcoString>,
    ) -> Result<(), R::Error> {
        pp.igroup(0, |pp| {
            for tree in &self.inner {
                tree.pretty(pp)?;
                pp.space()?;
            }
            Ok(())
        })
    }
}

impl Display for TokenStream {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut pp = Printer::new_with(String::new(), 120);
        self.pretty(&mut pp).unwrap();
        write!(f, "{}", pp.finish().unwrap())
    }
}

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
enum TokenUnit {
    #[token("(")]
    ParenOpen,

    #[token(")")]
    ParenClose,

    #[token("{")]
    BraceOpen,

    #[token("}")]
    BraceClose,

    #[token("[")]
    BracketOpen,

    #[token("]")]
    BracketClose,

    #[token("[[")]
    DoubleBracketOpen,

    #[token("]]")]
    DoubleBracketClose,

    #[regex(r"[\p{gc:Pc}\p{gc:Pd}\p{gc:Po}\p{gc:S}]", |lex|lex.slice().chars().next().unwrap())]
    Punct(char),

    #[regex(r"\p{XID_Start}\p{XID_Continue}*", |lex| EcoString::from(lex.slice()), priority = 3)]
    Ident(EcoString),

    #[regex(r"[1-9]['0-9]*|0", |lex| lex_integers(lex, Base::Decimal))]
    #[regex(r"0[bB]['01]+", |lex| lex_integers(lex, Base::Binary))]
    #[regex(r"0['0-7]+", |lex| lex_integers(lex, Base::Octal))]
    #[regex(r"0[xX]['0-9a-fA-F]+", |lex| lex_integers(lex, Base::Hexadecimal))]
    Integer((EcoString, Base, IntSuffix)),

    #[regex(r"['0-9]+[eE][+-]?['0-9]+", |lex| lex_floats(lex, FloatBase::Decimal))]
    #[regex(r"['0-9]*\.['0-9]+([eE][+-]?['0-9]+)?", |lex| lex_floats(lex, FloatBase::Decimal))]
    #[regex(r"0[xX]['0-9a-fA-F]+(\.['0-9a-fA-F]+)?[pP][+-]?['0-9]+", |lex| lex_floats(lex, FloatBase::Hexadecimal))]
    Float((EcoString, FloatBase, FloatSuffix)),

    #[regex(r"'", |lex| lex_char(lex, StrPrefix::None), priority = 3)]
    #[regex(r"u8'", |lex| lex_char(lex, StrPrefix::Utf8))]
    #[regex(r"u'", |lex| lex_char(lex, StrPrefix::Utf16))]
    #[regex(r"U'", |lex| lex_char(lex, StrPrefix::Utf32))]
    #[regex(r"L'", |lex| lex_char(lex, StrPrefix::Wide))]
    Char((EcoString, StrPrefix, bool)),

    #[regex(r#"""#, |lex| lex_string(lex, StrPrefix::None), priority = 3)]
    #[regex(r#"u8""#, |lex| lex_string(lex, StrPrefix::Utf8))]
    #[regex(r#"u""#, |lex| lex_string(lex, StrPrefix::Utf16))]
    #[regex(r#"U""#, |lex| lex_string(lex, StrPrefix::Utf32))]
    #[regex(r#"L""#, |lex| lex_string(lex, StrPrefix::Wide))]
    Str((EcoString, StrPrefix, bool)),

    #[token("true", |lex| {(EcoString::from(lex.slice()), true)})]
    #[token("false", |lex| {(EcoString::from(lex.slice()), false)})]
    Bool((EcoString, bool)),

    #[token("nullptr")]
    Nullptr,

    #[regex(r"[\p{White_Space}\t\n]+")]
    Whitespace,

    #[regex("//[^\n]*")]
    #[regex("/\\*([^*]|\\*[^/])*\\*/")]
    Comment,
}

/// Base of numeric literal encoding according to its prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Base {
    /// Literal starts with "0b".
    Binary = 2,
    /// Literal starts with "0".
    Octal = 8,
    /// Literal doesn't contain a prefix.
    Decimal = 10,
    /// Literal starts with "0x".
    Hexadecimal = 16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IntSuffix {
    unsigned: bool,
    long: Option<IntLong>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntLong {
    Long,
    LongLong,
    BitPrecise,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatSuffix {
    long: Option<FloatLong>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatLong {
    Float,
    LongDouble,
}

fn lex_integers(lex: &mut Lexer<TokenUnit>, base: Base) -> (EcoString, Base, IntSuffix) {
    #[derive(Logos)]
    pub enum IntSuffixRaw {
        None,

        #[regex("u|U")]
        Unsigned,

        #[regex("l|L")]
        Long,

        #[regex("ll|LL")]
        LongLong,

        #[regex("Ul|UL|lu|LU")]
        UnsignedLong,

        #[regex("Ull|ULL|llu|LLU")]
        UnsignedLongLong,

        #[regex("wb|WB")]
        BitPrecise,

        #[regex("uwb|UWB|wbu|WBU")]
        UnsignedBitPrecise,
    }

    impl From<IntSuffixRaw> for IntSuffix {
        #[inline]
        fn from(value: IntSuffixRaw) -> Self {
            let mut suffix = IntSuffix {
                unsigned: false,
                long: None,
            };
            if matches!(
                value,
                IntSuffixRaw::Unsigned
                    | IntSuffixRaw::UnsignedLong
                    | IntSuffixRaw::UnsignedLongLong
                    | IntSuffixRaw::UnsignedBitPrecise
            ) {
                suffix.unsigned = true;
            }
            suffix.long = match value {
                IntSuffixRaw::Long | IntSuffixRaw::UnsignedLong => Some(IntLong::Long),
                IntSuffixRaw::LongLong | IntSuffixRaw::UnsignedLongLong => Some(IntLong::LongLong),
                IntSuffixRaw::BitPrecise | IntSuffixRaw::UnsignedBitPrecise => {
                    Some(IntLong::BitPrecise)
                }
                _ => None,
            };
            suffix
        }
    }

    let value = EcoString::from(lex.slice());
    let mut suffix_lex = lex.clone().morph::<IntSuffixRaw>();
    if let Some(Ok(suffix)) = suffix_lex.next() {
        *lex = suffix_lex.morph();
        (value, base, suffix.into())
    } else {
        (value, base, IntSuffixRaw::None.into())
    }
}

/// Base of numeric literal encoding according to its prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatBase {
    /// Literal doesn't contain a prefix.
    Decimal = 10,
    /// Literal starts with "0x".
    Hexadecimal = 16,
}

fn lex_floats(lex: &mut Lexer<TokenUnit>, base: FloatBase) -> (EcoString, FloatBase, FloatSuffix) {
    #[derive(Logos)]
    pub enum FloatSuffixRaw {
        None,

        #[regex("f|F")]
        Float,

        #[regex("l|L")]
        LongDouble,
    }

    impl From<FloatSuffixRaw> for FloatSuffix {
        #[inline]
        fn from(value: FloatSuffixRaw) -> Self {
            let mut suffix = FloatSuffix { long: None };
            suffix.long = match value {
                FloatSuffixRaw::Float => Some(FloatLong::Float),
                FloatSuffixRaw::LongDouble => Some(FloatLong::LongDouble),
                _ => None,
            };
            suffix
        }
    }

    let value = EcoString::from(lex.slice());
    let mut suffix_lex = lex.clone().morph::<FloatSuffixRaw>();
    if let Some(Ok(suffix)) = suffix_lex.next() {
        *lex = suffix_lex.morph();
        (value, base, suffix.into())
    } else {
        (value, base, FloatSuffixRaw::None.into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StrPrefix {
    None,
    /// `u8`
    Utf8,
    /// `u`
    Utf16,
    /// `U`
    Utf32,
    /// `L`
    Wide,
}

fn lex_char(lex: &mut Lexer<TokenUnit>, prefix: StrPrefix) -> (EcoString, StrPrefix, bool) {
    #[derive(Logos)]
    enum CharInner<'a> {
        #[token("'", priority = 10)]
        End,

        #[regex(r"([^']|\\')+")]
        Content(&'a str),
    }

    let mut inner_lex = lex.clone().morph::<CharInner>();
    let mut content = EcoString::new();
    let mut terminated = false;
    for token in &mut inner_lex {
        match token {
            Ok(CharInner::End) => {
                terminated = true;
                break;
            }
            Ok(CharInner::Content(s)) => content.push_str(s),
            Err(_) => unreachable!(),
        }
    }
    *lex = inner_lex.morph();
    (content, prefix, terminated)
}

fn lex_string(lex: &mut Lexer<TokenUnit>, prefix: StrPrefix) -> (EcoString, StrPrefix, bool) {
    #[derive(Logos)]
    enum StrInner<'a> {
        #[token("\"", priority = 10)]
        End,

        #[regex(r#"([^"]|\\")+"#)]
        Content(&'a str),
    }

    let mut inner_lex = lex.clone().morph::<StrInner>();
    let mut content = EcoString::new();
    let mut terminated = false;
    for token in &mut inner_lex {
        match token {
            Ok(StrInner::End) => {
                terminated = true;
                break;
            }
            Ok(StrInner::Content(s)) => content.push_str(s),
            Err(_) => unreachable!(),
        }
    }
    *lex = inner_lex.morph();
    (content, prefix, terminated)
}
