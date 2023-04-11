# A vector of bits.
A dynamically sized `bit` array, with the underlying implementation being `Vec<u8>`, is designed to flexibly store a large number of `bool` types in a smaller space.
- Note that this does not include compression algorithms.
- Use bit operations for operations.

## Info
- crate: <https://crates.io/crates/bits_array>

# Examples
```rust
use bits_array::BitsArray;
let mut a = BitsArray::from([true, false, true, true, false]);
assert_eq!(a.get(4), Some(false));
assert_eq!(a.get(5), None);
assert_eq!(format!("{:b}", &a), "[10110000]");
a.push(true);
assert_eq!(format!("{:b}", &a), "[10110100]");
a.extend(a.clone());
assert_eq!(format!("{:b}", &a), "[10110110, 11010000]");
```
