# num-width

Trait to determine number width.

Example:

```rust
use num_width::NumberWidth;

assert_eq!(15u8.width(), 2);
assert_eq!((-7i8).signed_width(), 2);
```


