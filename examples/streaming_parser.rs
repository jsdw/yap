use std::{
    collections::VecDeque,
    fmt::Debug,
    io::{stdin, Read},
    iter::Iterator,
    sync::{Arc, Mutex},
};
use yap::{TokenLocation, Tokens};

/// Buffer over items of an iterator.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Buffer<Item> {
    oldest_elem_id: usize,
    elements: VecDeque<Option<Item>>,
    /// Sorted list of the oldest items needed per location
    checkout: Vec<usize>,
}

impl<Item> Default for Buffer<Item> {
    fn default() -> Self {
        Self {
            oldest_elem_id: Default::default(),
            elements: Default::default(),
            checkout: Default::default(),
        }
    }
}

/// Buffers over an iterator that can't itself be cloned.
/// Enables parsing a stream of values such such as from a network socket or other realtime source.
#[derive(Clone, Debug)]
pub struct BufferedTokens<I>
where
    I: Iterator,
{
    iter: I,
    cursor: usize,
    /// Shared buffer of items and the id of the oldest item in the buffer.
    buffer: Arc<Mutex<Buffer<I::Item>>>,
}

/// Token location that stores the changes since it was created for when the iterator is reset.
#[derive(Clone, Debug)]
pub struct BufferedTokensLocation<Item> {
    cursor: usize,
    buffer: Arc<Mutex<Buffer<Item>>>,
}

impl<Item> PartialEq for BufferedTokensLocation<Item> {
    fn eq(&self, other: &Self) -> bool {
        self.cursor == other.cursor && Arc::ptr_eq(&self.buffer, &other.buffer)
    }
}
impl<Item> Eq for BufferedTokensLocation<Item> {}

impl<Item> Drop for BufferedTokensLocation<Item> {
    fn drop(&mut self) {
        // Would rather not free memory then panic this thread because another panicked.
        if let Ok(mut buf) = self.buffer.lock() {
            let idx = buf
                .checkout
                .binary_search(&self.cursor)
                .expect("missing entry for location in checkout");
            buf.checkout.remove(idx);
        }
    }
}

impl<Item> TokenLocation for BufferedTokensLocation<Item> {
    fn offset(&self) -> usize {
        self.cursor
    }
}

impl<I: Iterator> BufferedTokens<I> {
    pub fn into_tokens(iter: I) -> Self {
        BufferedTokens {
            iter,
            cursor: Default::default(),
            buffer: Default::default(),
        }
    }
}

impl<I> Tokens for BufferedTokens<I>
where
    I: Iterator,
    I::Item: Clone + Debug,
{
    type Item = I::Item;

    type Location = BufferedTokensLocation<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor += 1;

        // Try buffer
        {
            let buf = self.buffer.lock().expect("not poisoned");
            // If buffer has elements use buffer before getting new elements.
            if let Some(val) = buf.elements.get(self.cursor - buf.oldest_elem_id).cloned() {
                return val;
            }
        }

        // Clear buffer of old values
        {
            let mut buf = self.buffer.lock().expect("not poisoned");
            // Remove old values no longer needed by any location
            let min = match buf.checkout.first() {
                Some(&x) => x.min(self.cursor),
                None => self.cursor,
            };
            while (buf.oldest_elem_id < min) && (!buf.elements.is_empty()) {
                buf.elements.pop_front();
                buf.oldest_elem_id += 1;
            }
        }

        // Handle cache miss
        {
            let next = self.iter.next();
            let mut buf = self.buffer.lock().expect("not poisoned");
            // Don't save to buffer if no locations exist which might need the value again
            if buf.checkout.is_empty() {
                return next;
            } else {
                buf.elements.push_back(next.clone());
                next
            }
        }
    }

    fn location(&self) -> Self::Location {
        // Checkout value at current location
        let mut buf = self.buffer.lock().expect("not poisoned");
        match buf.checkout.binary_search(&self.cursor) {
            Ok(x) => buf.checkout.insert(x, self.cursor),
            Err(x) => buf.checkout.insert(x, self.cursor),
        };
        BufferedTokensLocation {
            cursor: self.cursor,
            buffer: Arc::clone(&self.buffer),
        }
    }

    fn set_location(&mut self, location: Self::Location) {
        // Update cursor to new value
        self.cursor = location.cursor;
        // Location removes itself from checkout on drop
    }

    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.cursor == location.cursor
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
fn line_ending(tokens: &mut impl Tokens<Item = u8>) -> Option<&'static str> {
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
    // Parse pairs of digits into their sum. Stop parsing when a non-pair of digits is encountered.
    for line_of_digits in tokens.sep_by(
        |t| Some(t.many(|t| parse_digit_pair(t)).collect::<Vec<_>>()),
        |t| line_ending(t).is_some(),
    ) {
        println!("Line of digits: {:?}", line_of_digits);
    }
    // Reset location to show usage of internal buffer and freeing memory once the location doesn't need a diff buffer.
    tokens.set_location(start);
    // Internal buffer is cleared since there are no longer locations which need the items.
    while let Some(x) = tokens.as_iter().next() {
        println!("Element: {x}");
        if tokens
            .buffer
            .lock()
            .expect("not poisoned")
            .elements
            .is_empty()
        {
            break;
        }
    }
}
