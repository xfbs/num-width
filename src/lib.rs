//! Traits to determine the width of a number.

/// Determine the width needed to display a number.
pub trait NumberWidth {
    /// Digit count in the given base.
    ///
    /// This is expected to be zero for the number zero, and negative for negative numbers.
    fn signed_digit_count(&self, base: u64) -> isize;

    /// Width including leading minus sign if the number is negative.
    ///
    /// # Example
    ///
    /// ```rust
    /// use num_width::NumberWidth;
    /// assert_eq!(0u8.signed_width(), 1);
    /// assert_eq!(15u8.signed_width(), 2);
    /// assert_eq!((-33i8).signed_width(), 3);
    /// ```
    fn signed_width(&self) -> usize {
        self.signed_width_base(10)
    }

    /// Width of the number in the given base, including leading minus sign for negative numbers.
    ///
    /// # Example
    ///
    /// ```rust
    /// use num_width::NumberWidth;
    /// assert_eq!(0xAu8.signed_width_base(16), 1);
    /// assert_eq!(0xFFu8.signed_width_base(16), 2);
    /// assert_eq!((-0xAAi16).signed_width_base(16), 3);
    /// ```
    fn signed_width_base(&self, base: u64) -> usize {
        let count = match self.signed_digit_count(base) {
            count if count < 0 => (-count + 1) as usize,
            count => count as usize,
        };

        count.max(1)
    }

    /// Width needed to represent number.
    ///
    /// This does not include the width needed for a leading minus sign in case the number is
    /// negative. If that is what you need, consider using the [signed_width()][] method.
    ///
    /// # Example
    ///
    /// ```rust
    /// use num_width::NumberWidth;
    /// assert_eq!(0u8.width(), 1);
    /// assert_eq!(15u8.width(), 2);
    /// assert_eq!((-33i8).width(), 2);
    /// ```
    fn width(&self) -> usize {
        self.width_base(10)
    }

    /// Width needed to represent number in the given base.
    ///
    /// This does not include the width needed for a leading minus sign in case the number is
    /// negative. If that is what you need, consider using the [signed_width_base()][] method.
    fn width_base(&self, base: u64) -> usize {
        (self.signed_digit_count(base).abs() as usize).max(1)
    }
}

fn digit_count(num: u64, base: u64) -> usize {
    let mut width = 0;
    let mut cur = num;
    while cur > 0 {
        cur /= base;
        width += 1;
    }
    width
}

#[test]
fn test_digit_count() {
    for base in 2..255 {
        // zero always has count of zero
        assert_eq!(digit_count(0, base), 0);
        for num in 1..base {
            assert_eq!(digit_count(num, base), 1);
        }

        // test positive digit counts
        let mut num: u64 = 1;
        for i in 1.. {
            num = match num.checked_mul(base) {
                Some(num) => num,
                None => break,
            };
            assert_eq!(digit_count(num - 1, base), i);
            assert_eq!(digit_count(num, base), i + 1);
        }
    }
}

fn signed_digit_count(num: i64, base: u64) -> isize {
    let sign = num.signum() as isize;
    // using just abs() here will panic when num is i64::MIN.
    let num = num.checked_abs().map(|num| num as u64).unwrap_or(i64::MAX as u64 + 1);
    let digit_count = digit_count(num, base);
    digit_count as isize * sign
}

#[test]
fn test_signed_digit_count() {
    for base in 2..255 {
        // zero always has count of zero
        assert_eq!(signed_digit_count(0, base), 0);
        for num in 1..base {
            assert_eq!(signed_digit_count(num as i64, base), 1);
        }

        // test positive digit counts
        let mut num: i64 = 1;
        for i in 1.. {
            num = match num.checked_mul(base as i64) {
                Some(num) => num,
                None => break,
            };

            assert_eq!(signed_digit_count(num - 1, base), i);
            assert_eq!(signed_digit_count(num, base), i + 1);
        }

        // test negative digit counts
        let mut num: i64 = -1;
        for i in 1.. {
            num = match num.checked_mul(base as i64) {
                Some(num) => num,
                None => break,
            };

            assert_eq!(signed_digit_count(num + 1, base), -i);
            assert_eq!(signed_digit_count(num, base), -i - 1);
        }
    }
}

#[test]
fn can_determine_width_u8() {
    for num in 0..u8::MAX {
        assert_eq!(num.width() as usize, num.to_string().len());
        assert_eq!(num.signed_width() as usize, num.to_string().len());
    }
}

#[test]
fn can_determine_width_u16() {
    for num in 0..u16::MAX {
        assert_eq!(num.width() as usize, num.to_string().len());
        assert_eq!(num.signed_width() as usize, num.to_string().len());
    }
}

#[test]
fn can_determine_width_u32() {
    assert_eq!(0u32.width(), 1);
    assert_eq!(10u32.width(), 2);
    assert_eq!(100u32.width(), 3);

    assert_eq!(0x0u32.width_base(16), 1);
    assert_eq!(0xFu32.width_base(16), 1);
    assert_eq!(0xFABu32.width_base(16), 3);
    assert_eq!(0xCAFEu32.width_base(16), 4);
}

#[test]
fn can_determine_width_u64() {
    assert_eq!(0u64.width(), 1);
    assert_eq!(10u64.width(), 2);
    assert_eq!(100u64.width(), 3);

    assert_eq!(0x0u64.width_base(16), 1);
    assert_eq!(0xFu64.width_base(16), 1);
    assert_eq!(0xFABu64.width_base(16), 3);
    assert_eq!(0xDEADBEEFu64.width_base(16), 8);
}

#[test]
fn can_determine_width_i8() {
    for num in i8::MIN..i8::MAX {
        assert_eq!(num.signed_width() as usize, num.to_string().len());
        if num >= 0 {
            assert_eq!(num.width() as usize, num.to_string().len());
        }
    }
}

#[test]
fn can_determine_width_i16() {
    for num in i16::MIN..i16::MAX {
        assert_eq!(num.signed_width() as usize, num.to_string().len());
        if num >= 0 {
            assert_eq!(num.width() as usize, num.to_string().len());
        }
    }
}

#[test]
fn can_determine_width_i32() {
    assert_eq!(0i32.width(), 1);
    assert_eq!(10i32.width(), 2);
    assert_eq!(100i32.width(), 3);
    assert_eq!((-233i32).width(), 3);
    assert_eq!((-233i32).signed_width(), 4);

    assert_eq!(0x0i32.width_base(16), 1);
    assert_eq!(0xFi32.width_base(16), 1);
    assert_eq!(0xFABi32.width_base(16), 3);
    assert_eq!(0xCAFEi32.width_base(16), 4);
    assert_eq!((-0xCAFEi32).signed_width_base(16), 5);
}

#[test]
fn can_determine_width_i64() {
    assert_eq!(0i64.width(), 1);
    assert_eq!(10i64.width(), 2);
    assert_eq!(100i64.width(), 3);
    assert_eq!((-233i64).width(), 3);
    assert_eq!((-233i64).signed_width(), 4);

    assert_eq!(0x0i64.width_base(16), 1);
    assert_eq!(0xFi64.width_base(16), 1);
    assert_eq!(0xFABi64.width_base(16), 3);
    assert_eq!(0xCAFEi64.width_base(16), 4);
    assert_eq!((-0xCAFEi64).signed_width_base(16), 5);
}

impl NumberWidth for u8 {
    fn signed_digit_count(&self, base: u64) -> isize {
        digit_count((*self).into(), base) as isize
    }
}

impl NumberWidth for u16 {
    fn signed_digit_count(&self, base: u64) -> isize {
        digit_count((*self).into(), base) as isize
    }
}

impl NumberWidth for u32 {
    fn signed_digit_count(&self, base: u64) -> isize {
        digit_count((*self).into(), base) as isize
    }
}

impl NumberWidth for u64 {
    fn signed_digit_count(&self, base: u64) -> isize {
        digit_count(*self, base) as isize
    }
}

impl NumberWidth for usize {
    fn signed_digit_count(&self, base: u64) -> isize {
        digit_count((*self) as u64, base) as isize
    }
}

impl NumberWidth for i8 {
    fn signed_digit_count(&self, base: u64) -> isize {
        signed_digit_count((*self).into(), base)
    }
}

impl NumberWidth for i16 {
    fn signed_digit_count(&self, base: u64) -> isize {
        signed_digit_count((*self).into(), base)
    }
}

impl NumberWidth for i32 {
    fn signed_digit_count(&self, base: u64) -> isize {
        signed_digit_count((*self).into(), base)
    }
}

impl NumberWidth for i64 {
    fn signed_digit_count(&self, base: u64) -> isize {
        signed_digit_count(*self, base)
    }
}

impl NumberWidth for isize {
    fn signed_digit_count(&self, base: u64) -> isize {
        signed_digit_count((*self) as i64, base)
    }
}
