use std::collections::HashMap;
use yap::{IntoTokens, TokenLocation, Tokens};

/// An example JSON parser. We don't handle every case (ie proper float
/// parsing and proper escape and unicode sequences in strings), but this
/// should at least provide an example of how to use `yap`.
fn main() {
    assert_eq!(parse("null"), Ok(Value::Null));
    assert_eq!(parse("true"), Ok(Value::Bool(true)));
    assert_eq!(parse("1"), Ok(Value::Number(1.0)));
    assert_eq!(parse("-2.123"), Ok(Value::Number(-2.123)));
    assert_eq!(parse("+2.123"), Ok(Value::Number(2.123)));
    assert_eq!(
        parse("\"hello\\t\\nthere\""),
        Ok(Value::String("hello\t\nthere".to_string()))
    );

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

    let m = HashMap::from_iter([
        ("hello".to_string(), Value::Number(2.0)),
        (
            "another".to_string(),
            Value::Array(vec![
                Value::Number(1.0),
                Value::Number(2.0),
                Value::Number(3.0),
            ]),
        ),
        ("more".to_string(), Value::Object(HashMap::new())),
    ]);
    assert_eq!(
        parse(r#"{ "hello": 2, "another": [1,2,3], "more" : {}}"#),
        Ok(Value::Object(m))
    );
}

/// Parse JSON from a string. Just a very thin wrapper around `value()`.
fn parse(s: &str) -> Result<Value, Error> {
    value(&mut s.into_tokens())
}

/// This is what we'll parse our JSON into.
#[derive(Clone, PartialEq, Debug)]
enum Value {
    Null,
    Number(f64),
    String(String),
    Bool(bool),
    Array(Vec<Value>),
    Object(HashMap<String, Value>),
}

/// Some errors that can be emitted if things go wrong.
/// In this example, each error has a start and end location
/// denoting where the issue is in the string.
#[derive(PartialEq, Debug)]
struct Error {
    // Start and end location of the error
    location: (usize, usize),
    // What was the nature of the error?
    kind: ErrorKind,
}

#[derive(PartialEq, Debug)]
enum ErrorKind {
    // No ']' seen while parsing array.
    ArrayNotClosed,
    // No '}' seen while parsing object.
    ObjectNotClosed,
    // Object field isn't a valid string.
    InvalidObjectField,
    // No ':' seen between object field and valud.
    MissingObjectFieldSeparator,
    // String escape char (ie char after \) isn't valid.
    InvalidEscapeChar(char),
    // the file ended while we were still parsing.
    UnexpectedEof,
    // We expect to see a digit here while parsing a number.
    DigitExpectedNext,
    // We didn't successfully parse any valid JSON at all.
    InvalidJson,
}

impl ErrorKind {
    fn at<T: TokenLocation>(self, start: T, end: T) -> Error {
        Error {
            location: (start.offset(), end.offset()),
            kind: self,
        }
    }
}

/// This is the `yap` entry point, and is responsible for parsing JSON values.
///
/// Try parsing each of the different types of value we know about,
/// and return the first error that we encounter, or a valid `Value`.
fn value(toks: &mut impl Tokens<Item = char>) -> Result<Value, Error> {
    // Return the first thing we parse successfully from our token stream,
    // mapping values into their `Value` container.
    let value = yap::one_of!(ts from toks;
        array(ts).map(|res| res.map(Value::Array)),
        string(ts).map(|res| res.map(Value::String)),
        object(ts).map(|res| res.map(Value::Object)),
        number(ts).map(|res| res.map(Value::Number)),
        bool(ts).map(|v| Ok(Value::Bool(v))),
        null(ts).then_some(Ok(Value::Null))
    );

    // No value? This means that the input doesn't begin with any valid JSON
    // character.
    match value {
        Some(r) => r,
        None => Err(ErrorKind::InvalidJson.at(toks.location(), toks.location())),
    }
}

/// Arrays start and end with [ and ], and contain JSON values, which we can
/// use our top level value parser to handle.
///
/// - `Some(Ok(values))` means we successfully parsed 0 or more array values.
/// - `Some(Err(e))` means that we hit an error parsing the array.
/// - `None` means that this wasn't an array and so nothing was parsed.
fn array(toks: &mut impl Tokens<Item = char>) -> Option<Result<Vec<Value>, Error>> {
    // Note the location of the start of the array.
    let start = toks.location();

    // Try to consume a '['. If we can't, we consume nothing and bail.
    if !toks.token('[') {
        return None;
    }
    skip_whitespace(&mut *toks);

    // Use our `value()` parser to parse each array value, separated by ','.
    let values: Vec<Value> = toks
        .sep_by(|t| value(t).ok(), |t| field_separator(t))
        .collect();

    skip_whitespace(&mut *toks);
    if !toks.token(']') {
        // Record the start and end location of the array in our error.
        return Some(Err(ErrorKind::ArrayNotClosed.at(start, toks.location())));
    }

    Some(Ok(values))
}

/// Objects begin with {, and then have 0 or more "field":value pairs (for which we just
/// lean on our string and value parsers to handle), and then should close with a }.
///
/// - `Some(Ok(values))` means we successfully parsed 0 or more object values.
/// - `Some(Err(e))` means that we hit an error parsing the object.
/// - `None` means that this wasn't an object and so nothing was parsed.
fn object(toks: &mut impl Tokens<Item = char>) -> Option<Result<HashMap<String, Value>, Error>> {
    // Note the location of the start of the object.
    let start = toks.location();

    // Try to consume a '{'. If we can't, we consume nothing and bail.
    if !toks.token('{') {
        return None;
    }
    skip_whitespace(&mut *toks);

    // Expect object fields like `name: value` to be separated like arrays are.
    let values: Result<HashMap<String, Value>, Error> = toks
        .sep_by(|t| object_field(t), |t| field_separator(t))
        .collect();

    // If we hit any errors above, return it.
    let Ok(values) = values else {
        return Some(values);
    };

    skip_whitespace(&mut *toks);
    if !toks.token('}') {
        // Record the start and end location of the object in our error.
        return Some(Err(ErrorKind::ObjectNotClosed.at(start, toks.location())));
    }

    Some(Ok(values))
}

/// Each object contains zero or more fields, which each have names and values.
///
/// - `Some(Ok((key, val)))` means we parsed a keyval field pair.
/// - `Some(Err(e))` means we hit some unrecoverable error.
/// - `None` means we parsed nothing and hit the end of the object.
fn object_field(toks: &mut impl Tokens<Item = char>) -> Option<Result<(String, Value), Error>> {
    if toks.peek() == Some('}') {
        return None;
    }
    let start = toks.location();

    // Any valid string is also a valid field name. If we don't find a
    // string here, or it fails to parse, we kick up a fuss.
    let name = match string(&mut *toks) {
        None => return Some(Err(ErrorKind::InvalidObjectField.at(start.clone(), start))),
        Some(Err(err)) => return Some(Err(err)),
        Some(Ok(s)) => s,
    };

    skip_whitespace(&mut *toks);
    if !toks.token(':') {
        let loc = toks.location();
        return Some(Err(
            ErrorKind::MissingObjectFieldSeparator.at(loc.clone(), loc)
        ));
    }
    skip_whitespace(&mut *toks);

    // And after the name comes some arbitrary value:
    let val = match value(&mut *toks) {
        Ok(val) => val,
        Err(e) => return Some(Err(e)),
    };

    Some(Ok((name, val)))
}

/// Some fairly naive parsing of strings which just manually iterates over tokens
/// to handle basic escapes and pushes them to a string.
///
/// - `None` if nothing consumed and not a string
/// - `Some(Ok(s))` if we parsed a string successfully
/// - `Some(Err(e))` if something went wrong parsing a string.
fn string(toks: &mut impl Tokens<Item = char>) -> Option<Result<String, Error>> {
    // Try to consume a '"'. If we can't, we consume nothing and bail.
    if !toks.token('"') {
        return None;
    }

    // manually iterate over chars and handle them as needed,
    // adding them to our string.
    let mut s = String::new();
    while let Some(char) = toks.next() {
        match char {
            // Handle escape chars (naively; ignore \uXXX for instance):
            '\\' => {
                let Some(escape_char) = toks.next() else {
                    let loc = toks.location();
                    return Some(Err(ErrorKind::UnexpectedEof.at(loc.clone(), loc)));
                };
                let substitute_char = match escape_char {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '"' => '"',
                    '\\' => '\\',
                    // If we don't recognise the escape char, return an error:
                    c => {
                        let loc = toks.location();
                        return Some(Err(ErrorKind::InvalidEscapeChar(c).at(loc.clone(), loc)));
                    }
                };
                s.push(substitute_char)
            }
            // String closed; return it!
            '"' => return Some(Ok(s)),
            // Some standard char; add it to our string.
            c => s.push(c),
        }
    }

    // The string should have been closed above; if we get this far, it hasn't
    // been, so return an error.
    let loc = toks.location();
    Some(Err(ErrorKind::UnexpectedEof.at(loc.clone(), loc)))
}

/// true or false; None if neither!
fn bool(toks: &mut impl Tokens<Item = char>) -> Option<bool> {
    yap::one_of!(toks;
        toks.tokens("true".chars()).then_some(true),
        toks.tokens("false".chars()).then_some(false)
    )
}

// Is null seen? None if not.
fn null(toks: &mut impl Tokens<Item = char>) -> bool {
    toks.tokens("null".chars())
}

/// Parse numbers. Here, we store the start location and then skip over tokens as long
/// as they are what we expect, bailing with `None` if something isn't right. At the end,
/// we gather all of the tokens we skipped over at once and parse them into a number.
///
/// See `CharTokens::f64` for more correct float parsing.
fn number(toks: &mut impl Tokens<Item = char>) -> Option<Result<f64, Error>> {
    let start = toks.location();

    // Look for the start of a number. return None if
    // we're not looking at a number. Consume the token
    // if it looks like the start of a number.
    let is_fst_number = match toks.peek()? {
        '-' | '+' => toks.next().map(|_| false),
        '0'..='9' => toks.next().map(|_| true),
        _ => None,
    }?;

    // Now, skip over digits. If none, then this isn't an number unless
    // the char above was a digit too.
    let num_skipped = toks.skip_while(|c| c.is_numeric());
    if num_skipped == 0 && !is_fst_number {
        let loc = toks.location();
        return Some(Err(ErrorKind::DigitExpectedNext.at(start, loc)));
    }

    // A number might have a '.1234' suffix, but if it doesn't, don't consume
    // anything. If it does but something went wrong, we'll get Some(Err) back.
    let suffix = toks.optional(|toks| {
        if !toks.token('.') {
            return None;
        }
        let num_digits = toks.skip_while(|c| c.is_numeric());
        if num_digits == 0 {
            let loc = toks.location();
            Some(Err(ErrorKind::DigitExpectedNext.at(start.clone(), loc)))
        } else {
            Some(Ok(()))
        }
    });

    // If we hit an error parsing the suffix, return it.
    if let Some(Err(e)) = suffix {
        return Some(Err(e));
    }

    // If we get this far, we saw a valid number. Just let Rust parse it for us.
    // We use a `String` buffer to accumulate the slice of tokens before parsing
    // by default, although `StrTokens` is optimised to avoid using it in this case.
    let end = toks.location();
    let n = toks
        .slice(start, end)
        .parse::<f64, String>()
        .expect("valid number expected here");

    Some(Ok(n))
}

fn skip_whitespace(toks: &mut impl Tokens<Item = char>) {
    toks.skip_while(|c| c.is_ascii_whitespace());
}

fn field_separator(toks: &mut impl Tokens<Item = char>) -> bool {
    toks.surrounded_by(|t| t.token(','), |t| skip_whitespace(t))
}
