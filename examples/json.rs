use std::collections::HashMap;
use yap::{IntoTokens, Tokens};

/// An example JSON parser. We don't handle every case (ie proper float
/// parsing and proper escape and unicode sequences in strings), but this
/// should at least provide an example of how to use `yap`.
fn main() {
    assert_eq!(parse("true"), Ok(Value::Bool(true)));
    assert_eq!(parse("1"), Ok(Value::Number(1.0)));
    assert_eq!(parse("-2.123"), Ok(Value::Number(-2.123)));
    assert_eq!(
        parse("[1,2,3]"),
        Ok(Value::Array(vec![
            Value::Number(1.0),
            Value::Number(2.0),
            Value::Number(3.0)
        ]))
    );
    assert_eq!(
        parse("[\"hello\", false, []]"),
        Ok(Value::Array(vec![
            Value::String("hello".to_string()),
            Value::Bool(false),
            Value::Array(Vec::new())
        ]))
    );

    let m = {
        let mut m = HashMap::new();
        m.insert("hello".to_string(), Value::Number(2.0));
        m.insert(
            "another".to_string(),
            Value::Array(vec![
                Value::Number(1.0),
                Value::Number(2.0),
                Value::Number(3.0),
            ]),
        );
        m.insert("more".to_string(), Value::Object(HashMap::new()));
        m
    };
    assert_eq!(
        parse(r#"{ "hello": 2, "another": [1,2,3], "more" : {}}"#),
        Ok(Value::Object(m))
    );
}

/// Parse JSON from a string!
fn parse(s: &str) -> Result<Value, Error> {
    value(&mut s.into_tokens())
}

/// This is what we'll parse our JSON into.
#[derive(Clone, PartialEq, Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Array(Vec<Value>),
    Object(HashMap<String, Value>),
}

/// Some errors that can be emitted if things go wrong.
#[derive(Clone, PartialEq, Debug)]
enum Error {
    InvalidJson,
    Array(ArrayError),
    String(StringError),
    Object(ObjectError),
}

/// Try parsing each of the different types of value we know about,
/// bailing if one of those types returns a non-recoverable error, or
/// trying the next if it errors in a recoverable way.
fn value(toks: &mut impl Tokens<Item = char>) -> Result<Value, Error> {
    // Return `None` if the error isn't fatal and we should try the next
    // parser. Return the result otherwise.
    fn maybe(res: Result<Value, Error>) -> Option<Result<Value, Error>> {
        match res {
            Err(Error::InvalidJson)
            | Err(Error::Array(ArrayError::ExpectedOpenSquareBracket))
            | Err(Error::String(StringError::ExpectedOpenDoubleQuote))
            | Err(Error::Object(ObjectError::ExpectedOpenCurlyBrace)) => None,
            res => Some(res),
        }
    }

    // Return the first thing we parse successfully from our token stream.
    let value = yap::one_of!(ts from toks;
        maybe(array(ts).map(Value::Array).map_err(Error::Array)),
        maybe(string(ts).map(Value::String).map_err(Error::String)),
        maybe(object(ts).map(Value::Object).map_err(Error::Object)),
        bool(ts).map(|v| Ok(Value::Bool(v))),
        number(ts).map(|v| Ok(Value::Number(v))),
    );

    // No value? a bunch of recoverable errors were hit; ultimately invalid input.
    match value {
        Some(r) => r,
        None => Err(Error::InvalidJson),
    }
}

fn skip_whitespace(toks: &mut impl Tokens<Item = char>) {
    toks.skip_tokens_while(|c| c.is_ascii_whitespace());
}

fn field_separator(toks: &mut impl Tokens<Item = char>) -> bool {
    toks.surrounded_by(|t| t.token(','), |t| skip_whitespace(t))
}

#[derive(Clone, PartialEq, Debug)]
enum ArrayError {
    ExpectedOpenSquareBracket,
    InputFinishedButArrayNotClosed,
}

/// Arrays start and end with [ and ], and contain JSON values, which we can
/// use our top level value parser to handle.
fn array(toks: &mut impl Tokens<Item = char>) -> Result<Vec<Value>, ArrayError> {
    if !toks.token('[') {
        return Err(ArrayError::ExpectedOpenSquareBracket);
    }
    skip_whitespace(&mut *toks);

    let values: Vec<Value> = toks
        .sep_by(|t| value(t).ok(), |t| field_separator(t))
        .collect();

    skip_whitespace(&mut *toks);
    if !toks.token(']') {
        return Err(ArrayError::InputFinishedButArrayNotClosed);
    }
    Ok(values)
}

#[derive(Clone, PartialEq, Debug)]
enum ObjectError {
    ExpectedOpenCurlyBrace,
    InputFinishedButObjectNotClosed,
}

/// Objects begin with {, and then have 0 or more "field":value pairs (for which we just
/// lean on our string and value parsers to handle), and then should close with a }.
fn object(toks: &mut impl Tokens<Item = char>) -> Result<HashMap<String, Value>, ObjectError> {
    if !toks.token('{') {
        return Err(ObjectError::ExpectedOpenCurlyBrace);
    }
    skip_whitespace(&mut *toks);

    let values: HashMap<String, Value> = toks
        .sep_by(|t| object_field(t), |t| field_separator(t))
        .collect();

    skip_whitespace(&mut *toks);
    if !toks.token('}') {
        return Err(ObjectError::InputFinishedButObjectNotClosed);
    }
    Ok(values)
}

fn object_field(toks: &mut impl Tokens<Item = char>) -> Option<(String, Value)> {
    let name = string(&mut *toks).ok()?;
    skip_whitespace(&mut *toks);
    if !toks.token(':') {
        return None;
    }
    skip_whitespace(&mut *toks);
    let val = value(&mut *toks).ok()?;
    Some((name, val))
}

#[derive(Clone, PartialEq, Debug)]
enum StringError {
    ExpectedOpenDoubleQuote,
    InputFinishedButStringNotClosed,
}

/// We ignore escape sequences and things, and just parse everything between
/// a pair of "'s, kicking up a fuss if the string isn't closed.
fn string(toks: &mut impl Tokens<Item = char>) -> Result<String, StringError> {
    if !toks.token('"') {
        return Err(StringError::ExpectedOpenDoubleQuote);
    }

    let s = toks.tokens_while(|&c| c != '"').collect();

    if !toks.token('"') {
        return Err(StringError::InputFinishedButStringNotClosed);
    }
    Ok(s)
}

/// true or false; None if neither!
fn bool(toks: &mut impl Tokens<Item = char>) -> Option<bool> {
    if toks.tokens("true".chars()) {
        Some(true)
    } else if toks.tokens("false".chars()) {
        Some(false)
    } else {
        None
    }
}

/// Numbers are maybe the most difficult thing to parse. Here, we store the start
/// location and then skip over tokens as long as they are what we expect, bailing with
/// `None` if something isn't right. At the end, we gather all of the tokens we skipped
/// over at once and parse them into a number.
///
/// A better parser could return specific errors depending on where we failed in our parsing.
fn number(toks: &mut impl Tokens<Item = char>) -> Option<f64> {
    // If anything fails, we consume nothing.
    toks.optional(|toks| {
        let start_pos = toks.location();

        // Maybe it starts with a minus sign.
        toks.token('-');

        // Now, skip over digits. If none, then this isn't an number.
        let num_digits = toks.skip_tokens_while(|c| c.is_numeric());
        if num_digits == 0 {
            return None;
        }

        // Next, optionally look for a '.' followed by 1 or more digits.
        toks.optional(|toks| {
            if !toks.token('.') {
                return None;
            }
            let num_digits = toks.tokens_while(|c| c.is_numeric()).count();
            if num_digits == 0 {
                None
            } else {
                Some(())
            }
        });

        // Grab our numeric digits at once and parse:
        let end_pos = toks.location();
        let n_str: String = toks.slice(start_pos, end_pos).collect();
        n_str.parse().ok()
    })
}
