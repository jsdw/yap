use yap::{ Tokens, IntoTokens };
use std::collections::HashMap;
use logos::Logos;

/// An example JSON parser. We don't handle every case (ie proper float
/// parsing and proper escape and unicode sequences in strings), but this
/// should at least provide an example of how to use `yap`.
/// 
/// Unlike `json.rs`, this example uses the excellent `logos` crate for 
/// tokenizing and then `yap` to parse the tokens into something more 
/// meaningful. Here, `yap` is working with `JsonToken`'s instead of chars.
fn main() {
    assert_eq!(parse("true"), Ok(Value::Bool(true)));
    assert_eq!(parse("1"), Ok(Value::Number(1.0)));
    assert_eq!(parse("-2.123"), Ok(Value::Number(-2.123)));
    assert_eq!(parse("[1,2,3]"), Ok(Value::Array(vec![
        Value::Number(1.0),
        Value::Number(2.0),
        Value::Number(3.0)
    ])));
    assert_eq!(parse("[\"hello\", false, []]"), Ok(Value::Array(vec![
        Value::String("hello".to_string()),
        Value::Bool(false),
        Value::Array(Vec::new())
    ])));

    let m = {
        let mut m = HashMap::new();
        m.insert("hello".to_string(), Value::Number(2.0));
        m.insert("another".to_string(), Value::Array(vec![
            Value::Number(1.0),
            Value::Number(2.0),
            Value::Number(3.0)
        ]));
        m.insert("more".to_string(), Value::Object(HashMap::new()));
        m
    };
    assert_eq!(parse(r#"{ "hello": 2, "another": [1,2,3], "more" : {}}"#), Ok(Value::Object(m)));
}

/// Parse JSON from a string!
fn parse(s: &str) -> Result<Value, Error> {
    // Step 1: tokenize using logos. Logos exposes location information
    // as well, which we could attach to each token if we wanted to preserve
    // it during the parsing phase.
    let toks: Vec<JsonToken> = JsonToken::lexer(s).collect();

    // Step 2: parse tokens with yap:
    value(&mut toks.into_tokens())
}

/// Tokens we parse from logos:
#[derive(Logos, Debug, PartialEq)]
enum JsonToken {
    #[regex(r"(-)?[0-9]+(\.[0-9]+)?", |lex| lex.slice().parse())]
    Number(f64),

    #[token("true")]
    True,
 
    #[token("false")]
    False,

    #[token(",")]
    Comma,

    #[token("{")]
    OpenCurly,

    #[token("}")]
    CloseCurly,

    #[token("[")]
    OpenSquare,

    #[token("]")]
    CloseSquare,

    #[token(":")]
    Colon,

    #[regex(r#""[^"]*""#, |lex| lex.slice().strip_suffix('"').unwrap().strip_prefix('"').unwrap().to_string())]
    String(String),

    #[regex(r"[ \t\n]+", logos::skip)]
    #[error]
    Error
}

// helper functions for parsing:
impl JsonToken {
    fn as_string(&self) -> Option<String> {
        match self {
            JsonToken::String(s) => Some(s.to_owned()),
            _ => None
        }
    }
    fn as_bool(&self) -> Option<bool> {
        match self {
            JsonToken::True => Some(true),
            JsonToken::False => Some(false),
            _ => None
        }
    }
    fn as_number(&self) -> Option<f64> {
        match self {
            JsonToken::Number(val) => Some(*val),
            _ => None
        }
    }
    fn is_comma(&self) -> bool {
        match self {
            JsonToken::Comma => true,
            _ => false
        }
    }
}

/// This is what we'll parse our JSON into.
#[derive(Clone,PartialEq,Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Array(Vec<Value>),
    Object(HashMap<String,Value>)
}

/// Some errors that can be emitted if things go wrong.
#[derive(Clone,PartialEq,Debug)]
enum Error {
    InvalidJson,
    Array(ArrayError),
    Object(ObjectError),
}

/// Try parsing each of the different types of value we know about,
/// bailing if one of those types returns a non-recoverable error, or
/// trying the next if it errors in a recoverable way.
fn value<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Result<Value, Error> {
    // Return `None` if the error isn't fatal and we should try the next
    // parser. Return the result otherwise.
    fn maybe(res: Result<Value,Error>) -> Option<Result<Value,Error>> {
        match res {
            Err(Error::InvalidJson) | 
            Err(Error::Array(ArrayError::ExpectedOpenSquareBracket)) |
            Err(Error::Object(ObjectError::ExpectedOpenCurlyBrace)) => None,
            res => Some(res)
        }
    }
    
    // Return the first thing we parse successfully from our token stream.
    let value = yap::one_of!(ts from toks;
        maybe(array(ts).map(Value::Array).map_err(Error::Array)),
        maybe(object(ts).map(Value::Object).map_err(Error::Object)),
        string(ts).map(|v| Ok(Value::String(v))),
        bool(ts).map(|v| Ok(Value::Bool(v))),
        number(ts).map(|v| Ok(Value::Number(v))),
    );

    // No value? a bunch of recoverable errors were hit; ultimately invalid input.
    match value {
        Some(r) => r,
        None => Err(Error::InvalidJson)
    }
}

#[derive(Clone,PartialEq,Debug)]
enum ArrayError {
    ExpectedOpenSquareBracket,
    InputFinishedButArrayNotClosed
}

/// Arrays start and end with [ and ], and contain JSON values, which we can
/// use our top level value parser to handle.
fn array<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Result<Vec<Value>,ArrayError> {
    if !toks.token(&JsonToken::OpenSquare) {
        return Err(ArrayError::ExpectedOpenSquareBracket);
    }

    let values: Vec<Value> = toks.sep_by(
        |t| value(t).ok(),
        |t| t.next().map(|v| v.is_comma()).unwrap_or(false)
    ).collect();

    if !toks.token(&JsonToken::CloseSquare) {
        return Err(ArrayError::InputFinishedButArrayNotClosed);
    }
    Ok(values)
}

#[derive(Clone,PartialEq,Debug)]
enum ObjectError {
    ExpectedOpenCurlyBrace,
    InputFinishedButObjectNotClosed,
}

/// Objects begin with {, and then have 0 or more "field":value pairs (for which we just
/// lean on our string and value parsers to handle), and then should close with a }.
fn object<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Result<HashMap<String,Value>,ObjectError> {
    if !toks.token(&JsonToken::OpenCurly) {
        return Err(ObjectError::ExpectedOpenCurlyBrace);
    }

    let values: HashMap<String,Value> = toks.sep_by(
        |t| object_field(t),
        |t| t.token(&JsonToken::Comma)
    ).collect();

    if !toks.token(&JsonToken::CloseCurly) {
        return Err(ObjectError::InputFinishedButObjectNotClosed);
    }
    Ok(values)
}

fn object_field<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Option<(String,Value)> {
    let name = string(&mut *toks)?;

    if !toks.token(&JsonToken::Colon) {
        return None
    }

    let val = value(&mut *toks).ok()?;
    Some((name, val))
}

// We basically handle these in the tokenizing step, so nothing to do when parsing:

fn string<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Option<String> {
    toks.next().and_then(|t| t.as_string())
}

fn bool<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Option<bool> {
    toks.next().and_then(|t| t.as_bool())
}

fn number<'a>(toks: &mut impl Tokens<Item=&'a JsonToken>) -> Option<f64> {
    toks.next().and_then(|t| t.as_number())
}
