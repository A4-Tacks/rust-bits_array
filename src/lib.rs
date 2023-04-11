//! # Examples
//! ```
//! # use bits_array::BitsArray;
//! let mut a = BitsArray::from([true, false, true, true, false]);
//! assert_eq!(a.get(4), Some(false));
//! assert_eq!(a.get(5), None);
//! assert_eq!(format!("{:b}", &a), "[10110000]");
//! a.push(true);
//! assert_eq!(format!("{:b}", &a), "[10110100]");
//! a.extend(a.clone());
//! assert_eq!(format!("{:b}", &a), "[10110110, 11010000]");
//! ```


use std::{
    fmt::{
        self,
        Debug,
        Display,
        LowerHex,
        UpperHex,
        Binary
    },
    iter::Iterator,
    ops::Index,
};


pub const BYTE_FULL_MASK: u8 = u8::MAX;
pub const BYTE_FULL_MASK_USIZE: usize = BYTE_FULL_MASK as usize;
pub const BYTE_DIGIT: usize = 8;
pub const BYTE_DIGIT_MASK: usize = BYTE_DIGIT - 1;
pub const BYTE_DEFAULT: u8 = 0;


pub trait BitCtrl
    where Self: Sized,
          Self::Index: std::ops::Sub + ToOwned<Owned = usize>,
{
    type Index;
    fn get_bit(&self, idx: Self::Index) -> bool;
    fn write_true(&self, idx: Self::Index) -> Self;
    fn write_false(&self, idx: Self::Index) -> Self;
    fn write(&self, idx: Self::Index, val: bool) -> Self {
        if val {
            self.write_true(idx)
        } else {
            self.write_false(idx)
        }
    }
}


impl BitCtrl for u8 {
    type Index = usize;
    fn get_bit(&self, idx: Self::Index) -> bool {
        self >> idx & 1 == 1
    }
    fn write_true(&self, idx: Self::Index) -> Self {
        debug_assert!(idx < 8);
        self | 1 << idx
    }
    fn write_false(&self, idx: Self::Index) -> Self {
        debug_assert!(idx < 8);
        self & !(1 << idx)
    }
}


/// Storing Boolean values through byte arrays and providing some commonly used methods
/// Store Boolean values in each bit using bit operations.
/// `[low: low-order ... high: high-order]` `[[0], [1], [2], ...]`
/// # Examples
/// ```
/// # use bits_array::BitsArray;
/// let mut a = BitsArray::new();
/// a.push(false);
/// a.push(true);
/// a.push(false);
/// a.push(true);
/// a.push(true);
/// assert_eq!(a.borrow_bytes()[0], 0b11010);
/// ```
#[derive(Debug, Eq)]
pub struct BitsArray {
    /// bytes
    data: Vec<u8>,
    /// bits length
    len: usize,
}
impl BitsArray {
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let a = BitsArray::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
    /// Create a space for the number of bits beforehand
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let a = BitsArray::with_capacity(32);
    /// assert_eq!(a.borrow_bytes().capacity(), 4);
    /// for i in 33..40 {
    ///     let a = BitsArray::with_capacity(i);
    ///     assert_eq!(a.borrow_bytes().capacity(), 5);
    /// }
    /// # let a = BitsArray::with_capacity(31);
    /// # assert_eq!(a.borrow_bytes().capacity(), 4);
    /// # let a = BitsArray::with_capacity(40);
    /// # assert_eq!(a.borrow_bytes().capacity(), 5);
    /// ```
    pub fn with_capacity(bit_capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(Self::get_bits_capacity(bit_capacity)),
            len: 0,
        }
    }
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::with_capacity(32);
    /// unsafe {
    ///     a.set_len(11);
    ///     a.borrow_mut_bytes().resize(2, 0);
    /// }
    /// a.fill(true);
    /// assert_eq!(a.to_string(),
    ///     "[true, true, true, true, true, true, true, true, true, true, true]")
    /// ```
    pub fn fill(&mut self, value: bool) {
        let filler: u8 = if value { BYTE_FULL_MASK } else { 0 };
        self.data.fill(filler);
    }
    /// get length
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::new();
    /// a.push(true);
    /// a.push(true);
    /// a.push(false);
    /// assert_eq!(a.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn len_bits(&self) -> usize {
        self.len << 3
    }
    /// byte capacity
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }
    /// bits capacity
    pub fn capacity_bits(&self) -> usize {
        self.capacity() << 3
    }
    pub fn bytes_vec_len(&self) -> usize {
        self.data.len()
    }
    /// Obtain the `Bytes` required to store `N` `bits`
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// assert_eq!(BitsArray::get_bits_capacity(0), 0);
    /// for i in 1..=8 { assert_eq!(BitsArray::get_bits_capacity(i), 1) }
    /// for i in 9..=16 { assert_eq!(BitsArray::get_bits_capacity(i), 2) }
    /// ```
    pub fn get_bits_capacity(bit_capacity: usize) -> usize {
        Self::bitidx_to_byteidx(bit_capacity)
            + ( Self::bitidx_to_inbyte(bit_capacity) != 0) as usize
    }
    pub fn bitidx_to_byteidx(bitidx: usize) -> usize {
        bitidx >> 3
    }
    pub fn bitidx_to_inbyte(bitidx: usize) -> usize {
        bitidx & BYTE_DIGIT_MASK
    }
    /// Return(ByteIdx, BitIdx)
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// assert_eq!(BitsArray::bitidx_to_byteidx_and_bitidx(28), (3, 4));
    /// for i in 0..500 {
    ///     let res = BitsArray::bitidx_to_byteidx_and_bitidx(i);
    ///     assert_eq!(i, res.0 * 8 + res.1)
    /// }
    /// ```
    pub fn bitidx_to_byteidx_and_bitidx(bitidx: usize) -> (usize, usize) {
        (Self::bitidx_to_byteidx(bitidx), Self::bitidx_to_inbyte(bitidx))
    }
    /// push value to array end
    pub fn push(&mut self, value: bool) {
        let (byteidx, bitidx)
            = Self::bitidx_to_byteidx_and_bitidx(self.len);
        if byteidx >= self.data.len() {
            self.data.push(BYTE_DEFAULT)
        }
        self.len += 1;
        debug_assert!(byteidx < self.data.len());
        self.data[byteidx] = self.data[byteidx].write(bitidx, value);
    }
    /// pop array last value
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::new();
    /// a.push(true);
    /// a.push(false);
    /// assert_eq!(a.iter().collect::<Vec<_>>(), vec![true, false]);
    /// assert_eq!(a.pop(), Some(false));
    /// assert_eq!(a.pop(), Some(true));
    /// assert_eq!(a.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<bool> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        let (byteidx, bitidx)
            = Self::bitidx_to_byteidx_and_bitidx(self.len);
        Some(self.data[byteidx].get_bit(bitidx))
    }
    /// No need to check if the index is within the range of get
    pub unsafe fn unsafe_get(&self, idx: usize) -> bool {
        let (byteidx, bitidx)
            = Self::bitidx_to_byteidx_and_bitidx(idx);
        self.data[byteidx].get_bit(bitidx)
    }
    /// get array index value
    pub fn get(&self, idx: usize) -> Option<bool> {
        if idx >= self.len {
            return None;
        }
        Some(unsafe { self.unsafe_get(idx) })
    }
    /// set array index value
    pub fn set(&mut self, idx: usize, value: bool) {
        let (byteidx, bitidx)
            = Self::bitidx_to_byteidx_and_bitidx(idx);
        self.data[byteidx] = self.data[byteidx].write(bitidx, value);
    }
    /// Swap the values of two positions
    pub fn swap(&mut self, a: usize, b: usize) -> Result<(), String> {
        if !(a < self.len || b < self.len) {
            return Err(format!("index out of bounds: the len is {} but the index is {:?}",
                   self.len, (a, b)));
        }
        unsafe { self.unsafe_swap(a, b) }
        Ok(())
    }
    /// Swap the values of two positions without crossing the boundary check
    pub unsafe fn unsafe_swap(&mut self, a: usize, b: usize) {
        let (v1, v2) = unsafe {
            (self.unsafe_get(a), self.unsafe_get(b))
        };
        self.set(a, v2);
        self.set(b, v1);
    }
    /// get array iterator
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::new();
    /// a.push(true);
    /// a.push(false);
    /// assert_eq!(Vec::from_iter(a), vec![true, false]);
    /// ```
    pub fn iter(&self) -> Iter {
        Iter::from(self)
    }
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::new();
    /// a.push(true);
    /// a.push(false);
    /// a.push(true);
    /// a.push(true);
    /// assert_eq!(a.borrow_bytes()[0], 0b1101);
    /// ```
    pub fn borrow_bytes(&self) -> &Vec<u8> {
        &self.data
    }
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0)
    }
    /// Reduce the occupied space to the specified size as much as possible, in bits
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::new();
    /// for _ in 0..12 { a.push(true) }
    /// assert_eq!(a.bytes_vec_len(), 2);
    /// for _ in 0..6 { a.pop(); }
    /// assert_eq!(a.bytes_vec_len(), 2);
    /// a.shrink_to_fit();
    /// assert_eq!(a.bytes_vec_len(), 1);
    /// assert_eq!(a.get(5), Some(true));
    /// for _ in 0..6 { a.pop(); }
    /// a.shrink_to_fit();
    /// assert_eq!(a.bytes_vec_len(), 0);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let need_cap: usize
            = Self::get_bits_capacity(self.len);
        let min_capacity: usize
            = Self::get_bits_capacity(min_capacity);
        self.data.resize(need_cap.max(min_capacity), BYTE_DEFAULT);
        debug_assert!(Self::get_bits_capacity(self.len) <= self.bytes_vec_len());
    }
}
impl BitsArray { /* unsafe */
    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.len = new_len
    }
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::new();
    /// unsafe {
    ///     let borrow = a.borrow_mut_bytes();
    ///     assert_eq!(borrow.len(), 0);
    ///     borrow.push(0b111_10100);
    ///     a.set_len(5);
    /// }
    /// assert_eq!(a.to_string(), "[false, false, true, false, true]");
    /// ```
    pub unsafe fn borrow_mut_bytes(&mut self) -> &mut Vec<u8> {
        &mut self.data
    }
}
impl Default for BitsArray {
    fn default() -> Self {
        Self { data: Vec::new(), len: 0 }
    }
}
impl PartialEq for BitsArray {
    fn eq(&self, other: &Self) -> bool {
        let (slen, olen) = (self.len, other.len);
        slen == olen
            && {
                let last_byteidx: usize = Self::bitidx_to_byteidx(slen);
                self.data[0..last_byteidx] == other.data[0..last_byteidx]
                    && {
                        let in_lastbyte_bitidx: usize
                            = Self::bitidx_to_inbyte(slen);
                        macro_rules! get {
                            ( $t:expr ) => {
                                ($t).data[last_byteidx] as u16
                                    & (u8::MAX as u16
                                       >> (8 - in_lastbyte_bitidx))
                            };
                        }
                        get!(self) == get!(other)
                    }
            }
    }
}
impl<'a> FromIterator<&'a bool> for BitsArray {
    fn from_iter<T: IntoIterator<Item = &'a bool>>(iter: T) -> Self {
        let mut res = Self::new();
        for i in iter {
            res.push(*i)
        }
        res
    }
}
impl FromIterator<bool> for BitsArray {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut res = Self::new();
        for i in iter {
            res.push(i)
        }
        res
    }
}
impl From<&Vec<bool>> for BitsArray {
    fn from(value: &Vec<bool>) -> Self {
        let len = value.len();
        let mut res = Self::with_capacity(len);
        unsafe { res.set_len(len) }
        res.data.resize(res.data.capacity(), 0);
        for i in 0..len {
            res.set(i, value[i])
        }
        res
    }
}
impl From<Vec<bool>> for BitsArray {
    fn from(value: Vec<bool>) -> Self {
        Self::from(&value)
    }
}
impl From<&[bool]> for BitsArray {
    fn from(value: &[bool]) -> Self {
        let len = value.len();
        let mut res = Self::with_capacity(len);
        unsafe { res.set_len(len) }
        res.data.resize(res.data.capacity(), 0);
        for i in 0..len {
            res.set(i, value[i])
        }
        res
    }
}
impl From<&Self> for BitsArray {
    fn from(value: &Self) -> Self {
        Self { data: value.data.clone(), len: value.len }
    }
}
impl<const N: usize> From<&[bool; N]> for BitsArray {
    fn from(value: &[bool; N]) -> Self {
        Self::from(&value[..])
    }
}
impl<const N: usize> From<[bool; N]> for BitsArray {
    fn from(value: [bool; N]) -> Self {
        Self::from(&value)
    }
}
impl Display for BitsArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", Vec::from(self))
    }
}
impl IntoIterator for BitsArray {
    type Item = bool;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from(self)
    }
}
impl<'a> IntoIterator for &'a BitsArray {
    type Item = bool;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl From<&BitsArray> for Vec<bool> {
    fn from(value: &BitsArray) -> Self {
        let mut res = Vec::with_capacity(value.len());
        for i in value {
            res.push(i)
        }
        res
    }
}
impl From<BitsArray> for Vec<bool> {
    fn from(value: BitsArray) -> Self {
        Vec::from(&value)
    }
}
impl Extend<bool> for BitsArray {
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::from([true, true, false]);
    /// let b = BitsArray::from([true, false]);
    /// a.extend(b);
    /// assert_eq!(a, BitsArray::from([true, true, false, true, false]));
    /// ```
    fn extend<T: IntoIterator<Item = bool>>(&mut self, iter: T) {
        for i in iter {
            self.push(i)
        }
    }
}
impl<'a> Extend<&'a bool> for BitsArray {
    fn extend<T: IntoIterator<Item = &'a bool>>(&mut self, iter: T) {
        for i in iter {
            self.push(*i)
        }
    }
}
impl Clone for BitsArray {
    /// Use `From<&Self>`
    fn clone(&self) -> Self {
        Self::from(self)
    }
}
impl Index<usize> for BitsArray {
    type Output = bool;
    /// There will be some performance loss, if not desired, please use get
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let mut a = BitsArray::from([true, true, false]);
    /// assert_eq!(a.get(1).unwrap(), a[1]);
    /// assert_eq!(a.get(2).unwrap(), a[2]);
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        if self.get(index)
            .unwrap_or_else(|| panic!(
                    "index out of bounds: the len is {} but the index is {}",
                    self.len, index))
        {
            &true
        } else {
            &false
        }
    }
}
impl LowerHex for BitsArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fmtter: fn(x: &u8) -> String = if f.alternate() {
            fn func(x: &u8) -> String {
                format!("{:#02x}", x)
            }
            func
        } else {
            fn func(x: &u8) -> String {
                format!("{:02x}", x)
            }
            func
        };
        write!(f, "[{}]", self.data.iter()
               .map(fmtter).collect::<Vec<_>>()
               .join(", "))
    }
}
impl UpperHex for BitsArray {
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let a = BitsArray::from([true, false, false, true, false, true]);
    /// assert_eq!(format!("{:X}", a), "[29]");
    /// assert_eq!(format!("{:#X}", a), "[0x29]");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fmtter: fn(x: &u8) -> String = if f.alternate() {
            fn func(x: &u8) -> String {
                format!("{:#02X}", x)
            }
            func
        } else {
            fn func(x: &u8) -> String {
                format!("{:02X}", x)
            }
            func
        };
        write!(f, "[{}]", self.data.iter()
               .map(fmtter).collect::<Vec<_>>()
               .join(", "))
    }
}
impl Binary for BitsArray {
    /// get bytes binary (left low-order, right high-order)
    /// `5` -> `10100000`
    /// # Examples
    /// ```
    /// # use bits_array::BitsArray;
    /// let a = BitsArray::from([false, true, false]);
    /// assert_eq!(format!("{:b}", a), "[01000000]")
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]", self.data.iter()
               .map(|x| format!("{:08b}",
                                x.reverse_bits()))
               .collect::<Vec<_>>().join(", "))
    }
}


/// IntoIterator for BitsArray
pub struct IntoIter {
    target: BitsArray,
    idx: usize,
}
impl From<BitsArray> for IntoIter {
    fn from(value: BitsArray) -> Self {
        Self { target: value, idx: 0 }
    }
}
impl Iterator for IntoIter {
    type Item = bool;
    fn next(&mut self) -> Option<Self::Item> {
        let res = self.target.get(self.idx)?;
        self.idx += 1;
        Some(res)
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        // 跳过 n 个后 next
        self.idx += n;
        self.next()
    }
}

/// Iterator for BitsArray
pub struct Iter<'a> {
    target: &'a BitsArray,
    idx: usize,
}
impl<'a> From<&'a BitsArray> for Iter<'a> {
    fn from(value: &'a BitsArray) -> Self {
        Self { target: &value, idx: 0 }
    }
}
impl Iterator for Iter<'_> {
    type Item = bool;
    fn next(&mut self) -> Option<Self::Item> {
        let res = self.target.get(self.idx)?;
        self.idx += 1;
        Some(res)
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        // 跳过 n 个后 next
        self.idx += n;
        self.next()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example() {
        let mut a = BitsArray::from([true, false, true, true, false]);
        assert_eq!(a.get(4), Some(false));
        assert_eq!(a.get(5), None);
        assert_eq!(format!("{:b}", &a), "[10110000]");
        a.push(true);
        assert_eq!(format!("{:b}", &a), "[10110100]");
        a.extend(a.clone());
        assert_eq!(format!("{:b}", &a), "[10110110, 11010000]");
    }

    #[test]
    fn test_eq() {
        let a: BitsArray
            = BitsArray::from(vec![true, false, false, true, true]);
        let mut b: BitsArray
            = BitsArray::from(vec![true, false, false, true, true]);
        assert_eq!(&a, &b);
        b.pop();
        assert_ne!(&a, &b);
        b.push(false);
        assert_ne!(&a, &b);
        b.set(4, true);
        assert_eq!(&a, &b);
    }

    #[test]
    fn display() {
        let mut a: BitsArray
            = BitsArray::from(vec![true, false, false, true, true]);
        assert_eq!(a.to_string(), "[true, false, false, true, true]");
        a.pop();
        assert_eq!(a.to_string(), "[true, false, false, true]");
        a.push(false);
        assert_eq!(a.to_string(), "[true, false, false, true, false]");
        a.set(2, true);
        assert_eq!(a.to_string(), "[true, false, true, true, false]");
    }

    #[test]
    fn from_and_fromiter() {
        let data = vec![
            true, false, false, true, true, true, false, true, false, true];
        let a = BitsArray::from(&data);
        let b = BitsArray::from_iter(&data);
        assert_eq!(&a, &b);
    }

    #[test]
    fn debug() {
        let mut a = BitsArray::new();
        a.push(false);
        a.push(false);
        a.push(true);
        a.push(false);
        a.push(true);
        assert_eq!(format!("{:?}", a), "BitsArray { data: [20], len: 5 }");
    }

    #[test]
    fn get_and_set() {
        let mut a = BitsArray::new();
        a.push(false);
        a.push(false);
        a.push(true);
        a.push(false);
        assert_eq!(a.get(4), None);
        assert_eq!(a.get(0).unwrap(), false);
        assert_eq!(a.get(1).unwrap(), false);
        assert_eq!(a.get(2).unwrap(), true);
        assert_eq!(a.get(3).unwrap(), false);
        a.set(0, true);
        assert_eq!(a.get(0).unwrap(), true);
        a.set(3, true);
        assert_eq!(a.get(3).unwrap(), true);

        let mut a = BitsArray::new();
        let n = 28;
        for i in 0..n {
            a.push(i & 3 == 0);
        }
        for i in 0..n {
            assert_eq!(a.get(i).unwrap(), i & 3 == 0);
        }
    }

    #[test]
    fn push_and_pop() {
        let mut a = BitsArray::new();
        let n = 28;
        for i in 0..n {
            a.push(i & 3 == 0);
        }
        for i in (0..n).rev() {
            assert_eq!(a.pop().unwrap(), i & 3 == 0);
        }
        assert_eq!(a.pop(), None)
    }

    #[test]
    fn data_test() {
        let mut data = {vec![
            false, true, true, false, true, true, false, false, false, true,
            true, true, true, false, false, false, true, true, true, true,
            true, true, true, false, false, false, false, true, false, false,
            true, false, true, true, false, true, false, false, true, true,
            true, false, false, true, false, true, false, false, true, false,
            true, false, false, true, false, true, true, false, false, false,
            false, true, true, true, true, true, true, true, true, false,
            false, false, true, true, false, false, true, false, false, false,
            true, true, false, false, false, true, false, false, false, false,
            false, false, true, true, false, false, true, false, true, false
        ].repeat(100)};
        let mut out = Vec::with_capacity(data.len());
        let mut a = BitsArray::with_capacity(data.len());
        for _ in 0..1 {
            out.clear();
            for i in &data {
                a.push(*i)
            }
            for i in 0..data.len() {
                assert_eq!(a.get(i).unwrap(), *data.get(i).unwrap());
            }
            while let Some(i) = a.pop() {
                out.push(i)
            }
            out.reverse();
            assert_eq!(data, out);
            data.reverse();
        }
    }
}
