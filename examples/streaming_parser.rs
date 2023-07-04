use std::{
    fmt::Debug,
    io::{stdin, Read},
    iter::Iterator,
    ops::Deref,
    sync::{Arc, Mutex, Weak},
};
use yap::{TokenLocation, Tokens};

type SharedBuffer<T> = Vec<Arc<T>>;

#[derive(Clone, Debug)]
pub struct BufferedTokens<I>
where
    I: Iterator,
{
    iter: I,
    cursor: usize,
    buffer: SharedBuffer<Option<I::Item>>,
    /// - This list is used to broadcast new elements to all locations' buffers for when they are used to revert the iterator.
    /// - Weak references to locations so that they can be dropped when only referenced here.
    /// - The outer `Arc<Mutex<>>` is to get around the & in the location(&self) method.
    locs: Arc<Mutex<Vec<Weak<Mutex<BufferedTokensLocation<I::Item>>>>>>,
}

/// Token location that stores the changes since it was created for when the iterator is reset.
#[derive(Clone, Debug)]
pub struct BufferedTokensLocation<Item> {
    cursor: usize,
    buffer: SharedBuffer<Option<Item>>,
}

/// Newtype to allow defining a TokenLocation.
#[derive(Clone, Debug)]
pub struct SharedBufferedTokensLocation<Item> {
    inner: Arc<Mutex<BufferedTokensLocation<Item>>>,
}

impl<Item> Deref for SharedBufferedTokensLocation<Item> {
    type Target = Arc<Mutex<BufferedTokensLocation<Item>>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<Item> From<Arc<Mutex<BufferedTokensLocation<Item>>>> for SharedBufferedTokensLocation<Item> {
    fn from(value: Arc<Mutex<BufferedTokensLocation<Item>>>) -> Self {
        Self { inner: value }
    }
}

impl<I> TokenLocation for SharedBufferedTokensLocation<I> {
    fn offset(&self) -> usize {
        self.lock().unwrap().cursor
    }
}

impl<I: Iterator> BufferedTokens<I> {
    pub fn into_tokens(iter: I) -> Self {
        BufferedTokens {
            iter,
            cursor: Default::default(),
            buffer: Default::default(),
            locs: Default::default(),
        }
    }
}

impl<I> Tokens for BufferedTokens<I>
where
    I: Iterator,
    I::Item: Clone + Debug,
{
    type Item = I::Item;

    type Location = SharedBufferedTokensLocation<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor += 1;
        let mut locs = self.locs.lock().unwrap();
        // If buffer has elements empty buffer before getting new elements.
        if !self.buffer.is_empty() {
            self.buffer.remove(0).as_ref().clone()
        } else {
            let next = self.iter.next();
            let next_buffered = Arc::new(next.clone());
            let mut i = 0;
            while i < locs.len() {
                if let Some(loc) = locs[i].upgrade() {
                    loc.lock().unwrap().buffer.push(next_buffered.clone());
                    i += 1;
                } else {
                    // Location order doesn't matter because they are all broadcast to for new elements.
                    locs.swap_remove(i);
                }
            }
            next
        }
    }

    fn location(&self) -> Self::Location {
        let loc = Arc::new(Mutex::new(BufferedTokensLocation {
            cursor: self.cursor,
            buffer: self.buffer.clone(),
        }));
        self.locs.lock().unwrap().push(Arc::downgrade(&loc));
        loc.into()
    }

    fn set_location(&mut self, location: Self::Location) {
        // Sets all value necessary to reset the iterator.
        // It uses the location's store of buffered values.
        // Notice that the `locs` doesn't need to be changed because all locations should stay subscribed.
        let location = location.lock().unwrap();
        self.cursor = location.cursor;
        self.buffer = location.buffer.clone();
    }

    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.cursor == location.lock().unwrap().cursor
    }
}

/// Takes two digits and adds them together. Fails if there are not two base 10 digits.
fn parse_digit_pair(tokens: &mut impl Tokens<Item = u8>) -> Option<u32> {
    let d1 = tokens.next()? as char;
    let d2 = tokens.next()? as char;
    // Return the result of adding the 2 digits we saw:
    Some(d1.to_digit(10)? + d2.to_digit(10)?)
}

/// Parses a line ending of either "\r\n" (windows) or "\n" (linux)
fn line_ending(tokens: &mut impl Tokens<Item = u8>) -> Option<&str> {
    yap::one_of!(tokens;
        tokens.optional(|t| t.tokens("\r\n".chars().map(|x| u8::try_from(x).unwrap())).then_some("\r\n")),
        tokens.optional(|t| t.token(u8::try_from('\n').unwrap()).then_some("\n")),
    )
}

fn main() {
    let stdin = stdin().bytes().map(Result::unwrap);
    let mut tokens = BufferedTokens::into_tokens(stdin);
    // Set a location here to show how buffering works.
    let start = tokens.location();
    // Demonstrate streaming parsing of input.
    // This is relatively painless and looks the same as a non-streaming parser because `BufferedTokens` handles buffering and `Bytes<Stdin>` handles blocking.
    for line_of_digits in tokens.sep_by(
        |t| Some(t.many(|t| parse_digit_pair(t)).collect::<Vec<_>>()),
        |t| line_ending(t).is_some(),
    ) {
        println!("Line of digits: {:?}", line_of_digits);
    }
    // Reset location to show usage of internal buffer and freeing memory once the location doesn't need a diff buffer.
    tokens.set_location(start);
    let mut i = 0;
    // Internal buffer is cleared since there are no longer locations which need the items.
    loop {
        i += 1;
        // Speed up process by avoiding too many prints.
        if i % 1000 == 0 {
            eprintln!("Next: {:?}", tokens.next());
        }
        tokens.next();
        tokens.buffer.shrink_to_fit();
    }
}
