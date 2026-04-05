//! S-expression reader.
//!
//! Parses a string into rib-based Scheme values on the heap.
//! Symbols are interned via the shared SymbolTable.

use crate::heap::Heap;
use crate::symbol::SymbolTable;
use crate::val::Val;
use crate::table;

/// Reader state: a cursor into a source string.
pub struct Reader<'a> {
    src: &'a [u8],
    pos: usize,
}

/// Read error.
#[derive(Debug, PartialEq)]
pub enum ReadError {
    Eof,
    UnterminatedString,
    UnterminatedList,
    InvalidChar,
    InvalidHash,
}

type Result<T> = core::result::Result<T, ReadError>;

impl<'a> Reader<'a> {
    pub fn new(src: &'a str) -> Self {
        Reader { src: src.as_bytes(), pos: 0 }
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let c = self.src.get(self.pos).copied()?;
        self.pos += 1;
        Some(c)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(b' ' | b'\t' | b'\n' | b'\r') => { self.pos += 1; }
                Some(b';') => {
                    while let Some(c) = self.peek() {
                        self.pos += 1;
                        if c == b'\n' { break; }
                    }
                }
                _ => break,
            }
        }
    }

    fn is_delimiter(c: u8) -> bool {
        matches!(c, b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b'"' | b';')
    }

    /// Read one datum from the source.
    pub fn read(&mut self, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Val> {
        self.skip_whitespace_and_comments();

        match self.peek() {
            None => Err(ReadError::Eof),
            Some(b'(') => self.read_list(heap, syms),
            Some(b'"') => self.read_string(heap),
            Some(b'#') => self.read_hash(heap, syms),
            Some(b'\'') => self.read_abbrev(heap, syms, "quote"),
            Some(b'`') => self.read_abbrev(heap, syms, "quasiquote"),
            Some(b',') => {
                self.advance();
                if self.peek() == Some(b'@') {
                    self.advance();
                    self.read_abbrev_no_advance(heap, syms, "unquote-splicing")
                } else {
                    self.read_abbrev_no_advance(heap, syms, "unquote")
                }
            }
            Some(c) if c == b'-' || c == b'+' => {
                if self.pos + 1 < self.src.len()
                    && self.src[self.pos + 1].is_ascii_digit()
                {
                    self.read_number()
                } else {
                    self.read_symbol(heap, syms)
                }
            }
            Some(c) if c.is_ascii_digit() => self.read_number(),
            Some(_) => self.read_symbol(heap, syms),
        }
    }

    fn read_list(&mut self, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Val> {
        self.advance(); // consume '('
        self.skip_whitespace_and_comments();

        if self.peek() == Some(b')') {
            self.advance();
            return Ok(Val::NIL);
        }

        let first = self.read(heap, syms)?;
        self.skip_whitespace_and_comments();

        // Check for dotted pair
        if self.peek() == Some(b'.') {
            let dot_pos = self.pos;
            self.advance();
            if self.peek().map_or(true, Self::is_delimiter) {
                let cdr = self.read(heap, syms)?;
                self.skip_whitespace_and_comments();
                if self.peek() != Some(b')') {
                    return Err(ReadError::UnterminatedList);
                }
                self.advance();
                return Ok(heap.cons(first, cdr));
            } else {
                self.pos = dot_pos;
            }
        }

        let mut elems = Vec::new();
        elems.push(first);
        loop {
            self.skip_whitespace_and_comments();
            match self.peek() {
                None => return Err(ReadError::UnterminatedList),
                Some(b')') => {
                    self.advance();
                    break;
                }
                Some(b'.') => {
                    let dot_pos = self.pos;
                    self.advance();
                    if self.peek().map_or(true, Self::is_delimiter) {
                        let cdr = self.read(heap, syms)?;
                        self.skip_whitespace_and_comments();
                        if self.peek() != Some(b')') {
                            return Err(ReadError::UnterminatedList);
                        }
                        self.advance();
                        let mut result = cdr;
                        for &e in elems.iter().rev() {
                            result = heap.cons(e, result);
                        }
                        return Ok(result);
                    } else {
                        self.pos = dot_pos;
                        elems.push(self.read(heap, syms)?);
                    }
                }
                _ => {
                    elems.push(self.read(heap, syms)?);
                }
            }
        }

        let mut result = Val::NIL;
        for &e in elems.iter().rev() {
            result = heap.cons(e, result);
        }
        Ok(result)
    }

    fn read_number(&mut self) -> Result<Val> {
        let start = self.pos;
        if self.peek() == Some(b'-') || self.peek() == Some(b'+') {
            self.advance();
        }
        while self.peek().map_or(false, |c| c.is_ascii_digit()) {
            self.advance();
        }
        let s = core::str::from_utf8(&self.src[start..self.pos]).unwrap();
        let n: i64 = s.parse().unwrap();
        Ok(Val::fixnum(n))
    }

    fn read_symbol(&mut self, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Val> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if Self::is_delimiter(c) { break; }
            self.advance();
        }
        let name = core::str::from_utf8(&self.src[start..self.pos]).unwrap();
        Ok(syms.intern(name, heap))
    }

    fn read_string(&mut self, heap: &mut Heap) -> Result<Val> {
        self.advance(); // consume opening '"'
        let mut chars = Vec::new();
        loop {
            match self.advance() {
                None => return Err(ReadError::UnterminatedString),
                Some(b'"') => break,
                Some(b'\\') => {
                    match self.advance() {
                        Some(b'n') => chars.push(b'\n'),
                        Some(b't') => chars.push(b'\t'),
                        Some(b'\\') => chars.push(b'\\'),
                        Some(b'"') => chars.push(b'"'),
                        Some(c) => { chars.push(b'\\'); chars.push(c); }
                        None => return Err(ReadError::UnterminatedString),
                    }
                }
                Some(c) => chars.push(c),
            }
        }
        let mut char_list = Val::NIL;
        for &b in chars.iter().rev() {
            char_list = heap.cons(Val::fixnum(b as i64), char_list);
        }
        Ok(heap.string(char_list, Val::fixnum(chars.len() as i64)))
    }

    fn read_hash(&mut self, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Val> {
        self.advance(); // consume '#'
        match self.peek() {
            Some(b't') => {
                self.advance();
                if self.peek().map_or(true, Self::is_delimiter) {
                    Ok(heap.alloc_special(table::TRUE))
                } else {
                    self.pos -= 2;
                    self.read_symbol(heap, syms)
                }
            }
            Some(b'f') => {
                self.advance();
                if self.peek().map_or(true, Self::is_delimiter) {
                    Ok(heap.alloc_special(table::BOT))
                } else {
                    self.pos -= 2;
                    self.read_symbol(heap, syms)
                }
            }
            Some(b'\\') => {
                self.advance();
                self.read_character(heap)
            }
            Some(b'(') => self.read_vector(heap, syms),
            _ => Err(ReadError::InvalidHash),
        }
    }

    fn read_character(&mut self, heap: &mut Heap) -> Result<Val> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if Self::is_delimiter(c) { break; }
            self.advance();
        }
        let name = &self.src[start..self.pos];
        let cp = match name {
            b"space" => b' ' as i64,
            b"newline" => b'\n' as i64,
            b"tab" => b'\t' as i64,
            [c] => *c as i64,
            [] => return Err(ReadError::InvalidChar),
            _ => return Err(ReadError::InvalidChar),
        };
        Ok(heap.character(cp))
    }

    fn read_vector(&mut self, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Val> {
        self.advance(); // consume '('
        let mut elems = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            match self.peek() {
                None => return Err(ReadError::UnterminatedList),
                Some(b')') => { self.advance(); break; }
                _ => elems.push(self.read(heap, syms)?),
            }
        }
        let len = elems.len() as i64;
        let mut list = Val::NIL;
        for &e in elems.iter().rev() {
            list = heap.cons(e, list);
        }
        Ok(heap.vector(list, Val::fixnum(len)))
    }

    fn read_abbrev(&mut self, heap: &mut Heap, syms: &mut SymbolTable, name: &str) -> Result<Val> {
        self.advance();
        self.read_abbrev_no_advance(heap, syms, name)
    }

    fn read_abbrev_no_advance(&mut self, heap: &mut Heap, syms: &mut SymbolTable, name: &str) -> Result<Val> {
        let datum = self.read(heap, syms)?;
        let sym = syms.intern(name, heap);
        let inner = heap.cons(datum, Val::NIL);
        Ok(heap.cons(sym, inner))
    }

    /// Read all datums from the source.
    pub fn read_all(&mut self, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Vec<Val>> {
        let mut results = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek().is_none() { break; }
            results.push(self.read(heap, syms)?);
        }
        Ok(results)
    }
}

/// Convenience: read a single expression.
pub fn read(src: &str, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Val> {
    Reader::new(src).read(heap, syms)
}

/// Convenience: read all expressions.
pub fn read_all(src: &str, heap: &mut Heap, syms: &mut SymbolTable) -> Result<Vec<Val>> {
    Reader::new(src).read_all(heap, syms)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() -> (Heap, SymbolTable) {
        (Heap::new(), SymbolTable::new())
    }

    #[test]
    fn read_fixnum() {
        let (mut h, mut s) = setup();
        assert_eq!(read("42", &mut h, &mut s).unwrap(), Val::fixnum(42));
        assert_eq!(read("-7", &mut h, &mut s).unwrap(), Val::fixnum(-7));
        assert_eq!(read("0", &mut h, &mut s).unwrap(), Val::fixnum(0));
    }

    #[test]
    fn read_symbol() {
        let (mut h, mut s) = setup();
        let v = read("hello", &mut h, &mut s).unwrap();
        assert!(h.is_symbol(v));
    }

    #[test]
    fn read_symbol_interning() {
        let (mut h, mut s) = setup();
        let v1 = read("foo", &mut h, &mut s).unwrap();
        let v2 = read("foo", &mut h, &mut s).unwrap();
        assert_eq!(v1, v2); // same rib pointer — interned!
    }

    #[test]
    fn read_empty_list() {
        let (mut h, mut s) = setup();
        assert_eq!(read("()", &mut h, &mut s).unwrap(), Val::NIL);
    }

    #[test]
    fn read_list() {
        let (mut h, mut s) = setup();
        let v = read("(1 2 3)", &mut h, &mut s).unwrap();
        assert!(h.is_pair(v));
        assert_eq!(h.car(v), Val::fixnum(1));
        assert_eq!(h.car(h.cdr(v)), Val::fixnum(2));
        assert_eq!(h.car(h.cdr(h.cdr(v))), Val::fixnum(3));
    }

    #[test]
    fn read_nested_list() {
        let (mut h, mut s) = setup();
        let v = read("(1 (2 3) 4)", &mut h, &mut s).unwrap();
        assert_eq!(h.car(v), Val::fixnum(1));
        let inner = h.car(h.cdr(v));
        assert!(h.is_pair(inner));
        assert_eq!(h.car(inner), Val::fixnum(2));
    }

    #[test]
    fn read_dotted_pair() {
        let (mut h, mut s) = setup();
        let v = read("(1 . 2)", &mut h, &mut s).unwrap();
        assert_eq!(h.car(v), Val::fixnum(1));
        assert_eq!(h.cdr(v), Val::fixnum(2));
    }

    #[test]
    fn read_quote() {
        let (mut h, mut s) = setup();
        let v = read("'foo", &mut h, &mut s).unwrap();
        assert!(h.is_pair(v));
        let head = h.car(v);
        assert!(h.is_symbol(head));
    }

    #[test]
    fn read_string() {
        let (mut h, mut s) = setup();
        let v = read(r#""hello""#, &mut h, &mut s).unwrap();
        assert!(h.is_string(v));
    }

    #[test]
    fn read_character() {
        let (mut h, mut s) = setup();
        let v = read(r"#\a", &mut h, &mut s).unwrap();
        assert_eq!(h.tag(v), table::T_CHAR);
        assert_eq!(h.rib_car(v), Val::fixnum(b'a' as i64));
    }

    #[test]
    fn read_character_space() {
        let (mut h, mut s) = setup();
        let v = read(r"#\space", &mut h, &mut s).unwrap();
        assert_eq!(h.rib_car(v), Val::fixnum(b' ' as i64));
    }

    #[test]
    fn read_boolean_true() {
        let (mut h, mut s) = setup();
        let v = read("#t", &mut h, &mut s).unwrap();
        assert_eq!(h.tag(v), table::TRUE);
    }

    #[test]
    fn read_vector() {
        let (mut h, mut s) = setup();
        let v = read("#(1 2 3)", &mut h, &mut s).unwrap();
        assert!(h.is_vector(v));
    }

    #[test]
    fn read_comments() {
        let (mut h, mut s) = setup();
        let v = read("; comment\n42", &mut h, &mut s).unwrap();
        assert_eq!(v, Val::fixnum(42));
    }

    #[test]
    fn read_multiple() {
        let (mut h, mut s) = setup();
        let vs = read_all("1 2 (+ 3 4)", &mut h, &mut s).unwrap();
        assert_eq!(vs.len(), 3);
        assert_eq!(vs[0], Val::fixnum(1));
        assert_eq!(vs[1], Val::fixnum(2));
        assert!(h.is_pair(vs[2]));
    }
}
