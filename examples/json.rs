use yap::{ Tokens, IntoTokens };
use std::collections::HashMap;

fn main() {
    assert_eq!(parse("1"), Ok(Value::Number(1.0)));
}

#[derive(Clone,PartialEq,Debug)]
enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Array(Vec<Value>),
    Object(HashMap<String,Value>)
}

#[derive(Clone,PartialEq,Debug)]
enum Error {
    InvalidJson,
    Array(ArrayError),
    String(StringError),
    Object(ObjectError),
}

fn parse(s: &str) -> Result<Value, Error> {
    value(s.into_tokens())
}

fn value(mut toks: impl Tokens<Item=char>) -> Result<Value, Error> {
    // Return `None` to try the next parser, or `Some` to commit to this result.
    fn maybe(res: Result<Value,Error>) -> Option<Result<Value,Error>> {
        match res {
            Err(Error::InvalidJson) | 
            Err(Error::Array(ArrayError::ExpectedOpenSquareBracket)) |
            Err(Error::String(StringError::ExpectedOpenDoubleQuote)) |
            Err(Error::Object(ObjectError::ExpectedOpenCurlyBrace)) => None,
            res => Some(res)
        }
    }
    
    // Return the first thing we parse successfully from our token stream.
    let value = yap::one_of!(toks;
        maybe(array(toks).map(Value::Array).map_err(Error::Array)),
        maybe(string(toks).map(Value::String).map_err(Error::String)),
        maybe(object(toks).map(Value::Object).map_err(Error::Object)),
        bool(toks).map(|v| Ok(Value::Bool(v))),
        number(toks).map(|v| Ok(Value::Number(v))),
    );

    // If we didn't return a thing, we hit all of the non fatal errors,
    // so just return a generic invalid JSON error.
    match value {
        Some(r) => r,
        None => Err(Error::InvalidJson)
    }
}

fn skip_whitespace(mut toks: impl Tokens<Item=char>) {
    toks.skip_tokens_while(|c| c.is_ascii_whitespace());
}

fn field_separator(mut toks: impl Tokens<Item=char>) -> bool {
    toks.surrounded_by(
        |t| t.token(','),
        |t| skip_whitespace(t)
    )
}

#[derive(Clone,PartialEq,Debug)]
enum ArrayError {
    ExpectedOpenSquareBracket,
    InputFinishedButArrayNotClosed,
    FailedToParseValue(Box<Error>)
}

fn array(mut toks: impl Tokens<Item=char>) -> Result<Vec<Value>,ArrayError> {
    if !toks.token('[') {
        return Err(ArrayError::ExpectedOpenSquareBracket);
    }
    skip_whitespace(&mut toks);

    let values: Result<Vec<Value>,Error> = toks.sep_by_err(
        |t| value(t),
        |t| field_separator(t)
    ).collect();

    skip_whitespace(&mut toks);
    if !toks.token(']') {
        return Err(ArrayError::InputFinishedButArrayNotClosed);
    }
    values.map_err(Box::new).map_err(ArrayError::FailedToParseValue)
}

#[derive(Clone,PartialEq,Debug)]
enum ObjectError {
    ExpectedOpenCurlyBrace,
    InputFinishedButObjectNotClosed,
    ExpectedColon,
    FailedToParseField(StringError),
    FailedToParseValue(Box<Error>)
}

fn object_field(mut toks: impl Tokens<Item=char>) -> Result<(String,Value),ObjectError> {
    let name = string(&mut toks).map_err(ObjectError::FailedToParseField)?;
    skip_whitespace(&mut toks);
    if !toks.token(':') {
        return Err(ObjectError::ExpectedColon)
    }
    skip_whitespace(&mut toks);
    let val = todo!(); // value(&mut toks).map_err(Box::new).map_err(ObjectError::FailedToParseValue)?;
    Ok((name, val))
}

fn object(mut toks: impl Tokens<Item=char>) -> Result<HashMap<String,Value>,ObjectError> {
    if !toks.token('{') {
        return Err(ObjectError::ExpectedOpenCurlyBrace);
    }
    skip_whitespace(&mut toks);

    let values: Result<HashMap<String,Value>,ObjectError> = toks.sep_by_err(
        |t| object_field(t),
        |t| field_separator(t)
    ).collect();

    skip_whitespace(&mut toks);
    if !toks.token('}') {
        return Err(ObjectError::InputFinishedButObjectNotClosed);
    }
    values
}

#[derive(Clone,PartialEq,Debug)]
enum StringError {
    ExpectedOpenDoubleQuote,
    InputFinishedButStringNotClosed
}

fn string(mut toks: impl Tokens<Item=char>) -> Result<String,StringError> {
    if !toks.token('"') {
        return Err(StringError::ExpectedOpenDoubleQuote);
    }
    
    // Ignoring escape sequences and such:
    let s = toks.tokens_while(|&c| c != '"').collect();
    
    if !toks.token('"') {
        return Err(StringError::InputFinishedButStringNotClosed);
    }
    Ok(s)
}

fn bool(mut toks: impl Tokens<Item=char>) -> Option<bool> {
    if toks.tokens("true".chars()) {
        Some(true)
    } else if toks.tokens("false".chars()) {
        Some(false)
    } else {
        None
    }
}

fn number(mut toks: impl Tokens<Item=char>) -> Option<f64> {
    // If anything fails, we consume nothing.
    toks.optional(|toks| {
        let start_pos = toks.location();
    
        // We basically want to check for a number without actually
        // doing anything with the tokens; we'll grab all of the matching
        // tokens at once afterwards.
    
        // Maybe it starts with a minus sign.
        toks.token('-');
    
        // Now, skip over digits. If none, then this isn't an number.
        let num_digits = toks.skip_tokens_while(|c| c.is_numeric());
        if num_digits == 0 {
            return None
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
        let n_str: String = toks.iter_from_to(start_pos, end_pos).collect();
        n_str.parse().ok()
    })
}