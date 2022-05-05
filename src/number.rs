use anyhow::anyhow;
use anyhow::bail;
use anyhow::Error;
use lazy_static::lazy_static;
use regex::Regex;
use rug::Float;
use rug::Integer;
use rug::ops::NegAssign;
use rug::ops::Pow;
use rug::Rational;
use rug::ops::PowAssign;
use serde::Deserialize;
use serde::Serialize;
use static_assertions::const_assert;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::LowerExp;
use std::fmt::UpperExp;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;
use std::str::FromStr;
use unicode_normalization::UnicodeNormalization;

/// The precision, in binary digits, of floating point numbers. This value is
/// set to 250 binary digits (approximately 75.257 decimal digits).
const PRECISION: u32 = 250;

/// Archimedes' constant, pi, to at least `PRECISION` binary digits.
const STRING_PI: &str = "3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170680";

// Verify that `STRING_PI` is actually precise to at least `PRECISION` binary
// digits.
const_assert!((STRING_PI.len() - 2) as f64 * std::f64::consts::LOG2_10
>= PRECISION as f64);

lazy_static! {
    /// The `Float` (`PRECISION`-bit) closest to Archimedes' constant, pi.
    static ref PI: Float = Float::with_val(PRECISION, Float::parse(STRING_PI).unwrap());
}

/// Represents a number.
/// 
/// This structure represents a "number" for the purposes of this the converter.
/// This number may be exact or inexact (known only to a certain precision).
/// What exact numbers can be known exactly may change as the needs of the unit
/// converter changes: in its current incarnation, the following numbers can be
/// known exactly:
/// 
///   - Rational numbers;
///   - Rational multiples of pi; and
///   - Rational multiples of the reciprocal of pi;
/// 
/// There exist operations (most of them, actually) that are not closed over the
/// set of exact numbers. In this case, "relegation" occurs where the result of
/// such an operation on exact numbers is an inexact number.
#[derive(Clone, Deserialize, PartialEq, Serialize)]
pub struct Number {
    /// An implementing "class."
    class: Class,
}

/// Represents a number "class."
#[derive(Clone, Deserialize, PartialEq, Serialize)]
enum Class {
    /// Represents an exact number.
    Exact(
        /// The coefficient of the exponent of pi. This can only be zero if the
        /// exponent is also zero.
        Rational,

        /// The exponent of pi. This value must be {-1, 0, 1}.
        i32,
    ),

    /// Represents an inexact number.
    Inexact(
        /// The value of the number.
        Float,
    ),
}

impl Number {
    /// Returns the exact number 0.
    pub fn zero_exact() -> Number {
        Number {class: Class::Exact(Rational::new(), 0)}
    }

    /// Returns the exact number 1.
    pub fn one_exact() -> Number {
        Number {class: Class::Exact(Rational::from(1), 0)}
    }

    /// Assigns this number to its negation.
    pub fn neg_mut(&mut self) {
        match &mut self.class {
            Class::Exact(value, _) => {
                value.neg_assign();
            }
            Class::Inexact(value) => {
                value.neg_assign();
            }
        }
    }

    /// Returns the reciprocal of this number.
    pub fn recip(mut self) -> Number {
        self.recip_mut();
        self
    }

    /// Returns the reciprocal of this number.
    pub fn recip_ref(&self) -> Number {
        let mut operand = self.clone();
        operand.recip_mut();
        operand
    }

    /// Assigns this number to its reciprocal.
    pub fn recip_mut(&mut self) {
        match &mut self.class {
            Class::Exact(value, exponent) => {
                value.recip_mut();
                exponent.neg_assign();
            }
            Class::Inexact(value) => {
                value.recip_mut();
            }
        }
    }

    /// Returns this number raised to some exponent.
    pub fn pow(mut self, exponent: i32) -> Number {
        self.pow_mut(exponent);
        self
    }

    /// Returns this number raised to some exponent.
    pub fn pow_ref(&self, exponent: i32) -> Number {
        let mut base = self.clone();
        base.pow_mut(exponent);
        base
    }

    /// Assigns this number to itself raised to some exponent.
    pub fn pow_mut(&mut self, exponent: i32) {
        match &mut self.class {
            Class::Exact(value, exponent_self) => {
                value.pow_assign(exponent);
                exponent_self.mul_assign(exponent);

                if exponent_self.abs() > 1 {
                    let value = &*value * PI.clone().pow(*exponent_self);
                    self.class = Class::Inexact(value);
                }
            }
            Class::Inexact(value) => {
                if exponent == 0 {
                    self.class = Class::Exact(Rational::from(1), 0);
                }
                else {
                    value.pow_assign(exponent);
                }
            }
        }
    }
}

/// Implements parsing of strings into magnitudes.
impl FromStr for Number {
    type Err = Error;

    fn from_str(string: &str) -> Result<Number, Error> {
        enum Category {
            Rational,
            Pi,
            ReciprocalPi,
        }

        enum Sign {
            Nonnegative,
            Negative
        }

        lazy_static! {
            /// Possible regexes that a valid magnitude string can match with.
            static ref REGEXES: Vec<(Category, Sign, Regex)> = vec![
                // Strings of the form n.
                (Category::Rational, Sign::Nonnegative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]+)$"
                ).unwrap()),
                // Strings of the form n/d.
                (Category::Rational, Sign::Nonnegative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]+)$"
                ).unwrap()),
                // Strings of the form -(n/d).
                (Category::Rational, Sign::Negative, Regex::new(
                    r"^-\((?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]+)\)$"
                ).unwrap()),
                // String π. Yes, literally only this one case.
                (Category::Pi, Sign::Nonnegative, Regex::new(
                    r"^(?:π|pi)$"
                ).unwrap()),
                // String -π. Yes, literally only this one case too.
                (Category::Pi, Sign::Negative, Regex::new(
                    r"^-(?:π|pi)$"
                ).unwrap()),
                // Strings of the form nπ.
                (Category::Pi, Sign::Nonnegative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]*\d[\-\d\.Ee]*)(?:π|pi)$"
                ).unwrap()),
                // Strings of the form π(n).
                (Category::Pi, Sign::Nonnegative, Regex::new(
                    r"^(?:π|pi)\((?P<numerator>[\-\d\.Ee]+)\)$"
                ).unwrap()),
                // Strings of the form -π(n).
                (Category::Pi, Sign::Negative, Regex::new(
                    r"^-(?:π|pi)\((?P<numerator>[\-\d\.Ee]+)\)$"
                ).unwrap()),
                // Strings of the form π/d and nπ/d.
                (Category::Pi, Sign::Nonnegative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]+)?(?:π|pi)/(?P<denominator>[\-\d\.Ee]+)$"
                ).unwrap()),
                // Strings of the form (n/d)π.
                (Category::Pi, Sign::Nonnegative, Regex::new(
                    r"^\((?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]+)\)(?:π|pi)$"
                ).unwrap()),
                // Strings of the form -(n/d)π.
                (Category::Pi, Sign::Negative, Regex::new(
                    r"^-\((?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]+)\)(?:π|pi)$"
                ).unwrap()),
                // Strings of the form π(n/d).
                (Category::Pi, Sign::Nonnegative, Regex::new(
                    r"^(?:π|pi)\((?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]+)\)$"
                ).unwrap()),
                // Strings of the form -π(n/d).
                (Category::Pi, Sign::Negative, Regex::new(
                    r"^-(?:π|pi)\((?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]+)\)$"
                ).unwrap()),
                // Strings of the form n/π.
                (Category::ReciprocalPi, Sign::Nonnegative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]+)/(?:π|pi)$"
                ).unwrap()),
                // Strings of the form n/-π.
                (Category::ReciprocalPi, Sign::Negative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]+)/-(?:π|pi)$"
                ).unwrap()),
                // Strings of the form n/dπ.
                (Category::ReciprocalPi, Sign::Nonnegative, Regex::new(
                    r"^(?P<numerator>[\-\d\.Ee]+)/(?P<denominator>[\-\d\.Ee]*\d[\-\d\.Ee]*)(?:π|pi)$"
                ).unwrap()),
            ];
        }

        /// Parses the given number string into a rational number.
        fn parse_rational(string: &str) -> Result<Rational, Error> {
            lazy_static! {
                static ref REGEX_DECIMAL: Regex = Regex::new(
                    r"^(?P<integer>(?:-?\d*)?)\.?(?P<fraction>\d*)(?:[Ee](?P<exponent>-?\d+))?$"
                ).unwrap();
            }
            
            // Maybe it's faster to check if the string is a valid integer
            // before trying all the regex stuff.

            let captures = REGEX_DECIMAL.captures(string).ok_or_else(||
                anyhow!("Illegal number string")
            )?;

            let string_numerator = format!("{}{}", &captures["integer"], &captures["fraction"]);

            let mut numerator = string_numerator.parse::<Integer>().map_err(|_|
                anyhow!("Illegal number string")
            )?;

            let mut denominator = Integer::from(10).pow(captures["fraction"].len() as u32);

            if let Some(capture) = captures.name("exponent") {
                let exponent = capture.as_str().parse::<i32>().unwrap();
                let magnitude = Integer::from(10).pow(exponent.abs() as u32);

                if exponent > 0 {
                    numerator *= magnitude;
                }
                else {
                    denominator *= magnitude;
                }
            }

            Ok(Rational::from((numerator, denominator)))
        }

        // Perform Unicode dark magic.
        // 
        // In its current incarnation, this function will accept superscript and
        // subscript digits as valid numerals for the purpose of parsing. While
        // perhaps unintuitive given the normal use of superscript and subscript
        // digits, this behaviour is considered correct.
        let mut string = string.nfkc().collect::<String>();

        // Whitespace shall have no effect on the interpretation of number
        // strings.
        string.retain(|character| !character.is_whitespace());

        // Pursuant to resolution 10 of the 22nd CGPM, both the comma (,) and
        // the full stop (.) serve as the decimal separator.
        let string = string.replace(',', ".");

        // Perform number-specific compatibility "canonicalizations."
        let string = string.replace('\u{2212}', "-"); // `−`, minus sign.
        let string = string.replace('\u{2044}', "/"); // `⁄`, fraction slash.
        let string = string.replace('\u{2215}', "/"); // `∕`, division slash.

        // While not critical, it would be nice if the regexes were mutually
        // exclusive. It'd allow the regexes to be reordered without breaking
        // anything.
        debug_assert!({
            let mut hits = vec![];
            for (index, (_, _, regex)) in REGEXES.iter().enumerate() {
                if regex.is_match(&string) {
                    hits.push(index);
                }
            }
            hits.len() <= 1
        }, "Matched multiple regexes");

        // if let Ok(value) = string.parse::<BigInt>() {
        //     Ok(Magnitude::Rational(value.into()))
        // }
        // else if let Ok(value) = string.parse::<BigRational>() {
        //     Ok(Magnitude::Rational(value))
        // }
        // else if let Ok(value) = parse_number(&string) {
        //     Ok(Magnitude::Rational(value))
        // }
        if let Some((category, sign, regex))
        = REGEXES.iter().find(|(_, _, regex)| regex.is_match(&string)) {
            let mut category = category;
            let captures = regex.captures(&string).unwrap();

            // Finds the given capture group and parses it as a fraction part.
            let capture_part = |name: &str| -> Result<Rational, Error> {
                if let Some(capture) = captures.name(name) {
                    parse_rational(capture.as_str())
                }
                else {
                    Ok(Rational::from(1))
                }
            };

            let numerator = capture_part("numerator")?;
            let denominator = capture_part("denominator")?;

            let mut value = numerator / denominator;

            if let Sign::Negative = sign {
                value = -value;
            }

            if value.cmp0() == Ordering::Equal {
                category = &Category::Rational;
            }

            let exponent = match category {
                Category::Rational =>
                    0,
                Category::Pi =>
                    1,
                Category::ReciprocalPi =>
                    -1,
            };

            Ok(Number {class: Class::Exact(value, exponent)})
        }
        else {
            bail!("Illegal number string")
        }
    }
}

/// Implements computation of negation over numbers.
impl Neg for Number {
    type Output = Number;

    fn neg(mut self) -> Number {
        self.neg_mut();
        self
    }
}
impl Neg for &Number {
    type Output = Number;

    fn neg(self) -> Number {
        let mut operand = self.clone();
        operand.neg_mut();
        operand
    }
}

/// Implements computation of addition over numbers.
impl AddAssign<&Number> for Number {
    fn add_assign(&mut self, addend: &Number) {
        match (&mut self.class, &addend.class) {
            (Class::Exact(value_self, exponent_self), Class::Exact(value_addend, exponent_addend)) => {
                // Both addends are multiples of the same power of pi.
                if exponent_self == exponent_addend {
                    *value_self += value_addend;

                    if value_self.cmp0() == Ordering::Equal {
                        *exponent_self = 0;
                    }
                }
                // One of the addends is zero.
                else if value_self.cmp0() == Ordering::Equal
                || value_addend.cmp0() == Ordering::Equal {
                    // Because one of the addends is zero, this will have the
                    // effect of setting this number to the non-zero number.
                    *value_self += value_addend;
                    *exponent_self += exponent_addend;

                    debug_assert!(value_self.cmp0() != Ordering::Equal);
                }
                else {
                    let value = &*value_self * PI.clone().pow(&*exponent_self)
                    + value_addend * PI.clone().pow(*exponent_addend);
                    self.class = Class::Inexact(value);
                }
            }
            (Class::Exact(value_self, exponent_self), Class::Inexact(value_addend)) => {
                // TODO optimization may be possible for owned addend
                let value = &*value_self * PI.clone().pow(*exponent_self) + value_addend;
                self.class = Class::Inexact(value);
            }
            (Class::Inexact(value_self), Class::Exact(value_addend, exponent_addend)) => {
                *value_self += value_addend * PI.clone().pow(*exponent_addend);
            }
            (Class::Inexact(value_self), Class::Inexact(value_addend)) => {
                *value_self += value_addend;
            }
        }
    }
}

/// Implements computation of subtraction over numbers.
impl SubAssign<&Number> for Number {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn sub_assign(&mut self, subtrahend: &Number) {
        self.neg_mut();
        *self += subtrahend;
        self.neg_mut();
    }
}
impl Sub<Number> for &Number {
    type Output = Number;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, mut subtrahend: Number) -> Number {
        subtrahend.neg_mut();
        subtrahend += self;
        subtrahend
    }
}

/// Implements computation of multiplication over numbers.
impl MulAssign<&Number> for Number {
    fn mul_assign(&mut self, multiplicand: &Number) {
        match (&mut self.class, &multiplicand.class) {
            (Class::Exact(value_self, exponent_self), Class::Exact(value_multiplicand, exponent_multiplicand)) => {
                // TODO optimization may be possible by swapping one of the
                // passed in Rationals into the final one.
                *value_self *= value_multiplicand;
                *exponent_self += exponent_multiplicand;

                if value_self.cmp0() == Ordering::Equal {
                    *exponent_self = 0;
                }

                // In the future, we may relax this restriction and allow
                // numbers to be a multiple of any integer power of pi.
                if exponent_self.abs() > 1 {
                    let value = &*value_self * PI.clone().pow(*exponent_self);
                    self.class = Class::Inexact(value);
                }
            }
            (Class::Exact(value_self, exponent_self), Class::Inexact(value_multiplicand)) => {
                if value_self.cmp0() != Ordering::Equal {
                    // TODO optimization may be possible for owned multiplicand
                    let value = &*value_self * PI.clone().pow(*exponent_self) * value_multiplicand;
                    self.class = Class::Inexact(value);
                }
            }
            (Class::Inexact(value_self), Class::Exact(value_multiplicand, exponent_multiplicand)) => {
                if value_multiplicand.cmp0() == Ordering::Equal {
                    self.class = Class::Exact(Rational::new(), 0);
                }
                else {
                    *value_self *= value_multiplicand * PI.clone().pow(*exponent_multiplicand);
                }
            }
            (Class::Inexact(value_self), Class::Inexact(value_multiplicand)) => {
                *value_self *= value_multiplicand;
            }
        }
    }
}

/// Implements computation of division over numbers.
impl DivAssign<&Number> for Number {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, denominator: &Number) {
        match &self.class {
            // This number is already zero; do nothing.
            Class::Exact(value, _) if value.cmp0() == Ordering::Equal =>
                {}
            Class::Inexact(value) if value.cmp0() == Some(Ordering::Equal) =>
                {}

            _ => {
                self.recip_mut();
                *self *= denominator;
                self.recip_mut();
            }
        }
    }
}
impl Div<Number> for &Number {
    type Output = Number;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, mut denominator: Number) -> Number {
        denominator.recip_mut();
        denominator *= self;
        denominator
    }
}

/// Implements traits describing a non-commutative basic operation of arithmetic
/// on `Number` and `&Number`.
macro_rules! impl_arithmetic_noncommutative {
    ($trait:ident, $method:ident, $trait_assign:ident, $method_assign:ident) => {
        impl $trait_assign<Number> for Number {
            fn $method_assign(&mut self, operand_right: Number) {
                self.$method_assign(&operand_right);
            }
        }

        impl $trait<Number> for Number {
            type Output = Number;
        
            fn $method(mut self, operand_right: Number) -> Number {
                self.$method_assign(operand_right);
                self
            }
        }

        impl $trait<&Number> for Number {
            type Output = Number;
        
            fn $method(mut self, operand_right: &Number) -> Number {
                self.$method_assign(operand_right);
                self
            }
        }

        impl $trait<&Number> for &Number {
            type Output = Number;
        
            fn $method(self, operand_right: &Number) -> Number {
                let mut operand_left = self.clone();
                operand_left.$method_assign(operand_right);
                operand_left
            }
        }
    };
}

/// Implements traits describing a commutative basic operation of arithmetic on
/// `Number` and `&Number`.
macro_rules! impl_arithmetic_commutative {
    ($trait:ident, $method:ident, $trait_assign:ident, $method_assign:ident) => {
        impl_arithmetic_noncommutative!(
            $trait, $method, $trait_assign, $method_assign
        );

        impl $trait<Number> for &Number {
            type Output = Number;
        
            fn $method(self, mut operand_right: Number) -> Number {
                operand_right.$method_assign(self);
                operand_right
            }
        }
    }
}

impl_arithmetic_commutative!(Add, add, AddAssign, add_assign);
impl_arithmetic_noncommutative!(Sub, sub, SubAssign, sub_assign);
impl_arithmetic_commutative!(Mul, mul, MulAssign, mul_assign);
impl_arithmetic_noncommutative!(Div, div, DivAssign, div_assign);

/// Implements formatting of magnitudes as an exact value.
impl Display for Number {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        lazy_static! {
            static ref NEGATIVE_ONE: Integer = Integer::from(-1);
            static ref ONE: Integer = Integer::from(1);
        }

        match &self.class {
            Class::Exact(value, 0) => {
                write!(formatter, "{}", value)?;
            },
            Class::Exact(value, 1) => {
                if value.numer() == &*NEGATIVE_ONE {
                    write!(formatter, "-")?;
                }
                else if value.numer() != &*ONE {
                    write!(formatter, "{}", value.numer())?;
                }

                write!(formatter, "π")?;

                if !value.is_integer() {
                    write!(formatter, "/{}", value.denom())?;
                }
            },
            Class::Exact(value, -1) => {
                write!(formatter, "{}", value)?;

                if value.is_integer() {
                    write!(formatter, "/")?;
                }

                write!(formatter, "π")?;
            }
            Class::Exact(..) => {
                unreachable!();
            }
            Class::Inexact(value) => {
                // TODO honor formatter's desired precision

                write!(formatter, "{}", value)?;
            }
        }

        Ok(())
    }
}


// TODO refactor
/// Implements formatting of magnitudes as an exact value.
impl Debug for Number {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        lazy_static! {
            static ref NEGATIVE_ONE: Integer = Integer::from(-1);
            static ref ONE: Integer = Integer::from(1);
        }

        match &self.class {
            Class::Exact(value, 0) => {
                write!(formatter, "{}", value)?;
            },
            Class::Exact(value, 1) => {
                if value.numer() == &*NEGATIVE_ONE {
                    write!(formatter, "-")?;
                }
                else if value.numer() != &*ONE {
                    write!(formatter, "{}", value.numer())?;
                }

                write!(formatter, "π")?;

                if !value.is_integer() {
                    write!(formatter, "/{}", value.denom())?;
                }
            },
            Class::Exact(value, -1) => {
                write!(formatter, "{}", value)?;

                if value.is_integer() {
                    write!(formatter, "/")?;
                }

                write!(formatter, "π")?;
            }
            Class::Exact(_, _) => {
                unreachable!();
            }
            Class::Inexact(value) => {
                // TODO honor formatter's desired precision

                write!(formatter, "{}", value)?;
            }
        }

        Ok(())
    }
}



/// Implements traits for formatting magnitudes as an approximate value in
/// scientific notation.
macro_rules! impl_fmtexp {
    ($trait:ident, $separator:literal) => {
        impl $trait for Number {
            fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
                writeln!(formatter, "{}", $separator)?;

                todo!()
            }
        }
    };
}

impl_fmtexp!(LowerExp, 'e');
impl_fmtexp!(UpperExp, 'E');



#[cfg(test)]
mod tests {
    use super::*;

    use rstest::rstest;
    use std::f64::consts::PI;
    use std::panic;
    use std::panic::AssertUnwindSafe;

    /// Produces a rational number.
    fn rat(string: &str) -> Number {
        Number {class: Class::Exact(string.parse().unwrap(), 0)}
    }

    /// Produces a multiple-of-pi number.
    fn pi(string: &str) -> Number {
        let coefficient = string.parse::<Rational>().unwrap();
        assert!(coefficient.cmp0() != Ordering::Equal);
        Number {class: Class::Exact(coefficient, 1)}
    }

    /// Produces a multiple-of-inverse-pi number.
    fn rpi(string: &str) -> Number {
        let coefficient = string.parse::<Rational>().unwrap();
        assert!(coefficient.cmp0() != Ordering::Equal);
        Number {class: Class::Exact(coefficient, -1)}
    }

    /// Produces an inexact number.
    fn i(float: f64) -> Number {
        let value = Float::with_val(PRECISION, float);
        Number {class: Class::Inexact(value)}
    }

    /// Asserts that two numbers are equal (taking into account floating point
    /// equality).
    fn assert_number_eq(expected: &Option<Number>, actual: impl Fn() -> Number) {
        lazy_static! {
            static ref EPSILON: Float = Float::with_val(PRECISION, 10e-15);
        }

        let actual = panic::catch_unwind(AssertUnwindSafe(actual));

        match (expected, actual) {
            (None, Err(_)) => {
                // Pass.
            },
            (None, Ok(actual)) => {
                panic!("Expected panic\nActual: {}", actual);
            },
            (Some(expected), Err(_)) => {
                panic!("Expected: {}\nPanicked", expected); // TODO somehow print this message
            },
            (Some(expected), Ok(actual)) => {
                match (&expected.class, &actual.class) {
                    (Class::Inexact(value_expected), Class::Inexact(value_actual)) => {
                        if value_expected != value_actual {
                            assert!(
                                (value_expected.clone() - value_actual.clone()).abs() < *EPSILON,
                                "Expected: {}\nActual: {}\n(to within {})",
                                value_expected,
                                value_actual,
                                *EPSILON,
                            );
                        }
                    },
                    (_, _) => {
                        assert_eq!(expected, &actual);
                    },
                }
            },
        }
    }

    /// Tests the correctness of a unary arithmetic operation on numbers.
    macro_rules! test_operation_unary {
        (
            $name:ident,
            $method:ident,
            $method_ref:ident,
            $method_assign:ident,
            $(#$macros:tt)+
        ) => {
            $(
                #$macros
            )+
            fn $name(
                #[case] expected: Option<Number>,
                #[case] operand: Number
            ) {
                // Owned operand.
                assert_number_eq(&expected, || {
                    operand.clone().$method()
                });

                // Immutable reference operand.
                assert_number_eq(&expected, || {
                    (&operand).$method_ref()
                });

                // Mutable reference operand.
                assert_number_eq(&expected, || {
                    let mut operand = operand.clone();
                    operand.$method_assign();
                    operand
                });
            }
        }
    }

    /// Tests the correctness of a binary arithmetic operation on numbers.
    macro_rules! test_operation_binary {
        (
            $name:ident,
            $method:ident,
            $method_assign:ident,
            $(#$macros:tt)+
        ) => {
            $(
                #$macros
            )+
            fn $name(
                #[case] expected: Option<Number>,
                #[case] operand_left: Number,
                #[case] operand_right: Number
            ) {
                // Owned left- and right-hand operands.
                assert_number_eq(&expected, || {
                    operand_left.clone().$method(operand_right.clone())
                });

                // Owned left-hand and immutable reference right-hand operands.
                assert_number_eq(&expected, || {
                    operand_left.clone().$method(&operand_right)
                });

                // Immutable reference left-hand and owned right-hand operands.
                assert_number_eq(&expected, || {
                    (&operand_left).$method(operand_right.clone())
                });

                // Immutable reference left- and right-hand operands.
                assert_number_eq(&expected, || {
                    (&operand_left).$method(&operand_right)
                });

                // Mutable reference left-hand and owned right-hand operands.
                assert_number_eq(&expected, || {
                    let mut operand_left = operand_left.clone();
                    operand_left.$method_assign(operand_right.clone());
                    operand_left
                });

                // Mutable reference left-hand and immutable reference right-hand
                // operands.
                assert_number_eq(&expected, || {
                    let mut operand_left = operand_left.clone();
                    operand_left.$method_assign(&operand_right);
                    operand_left
                });
            }
        }
    }
    
    /// Tests parsing number strings.
    #[rstest]
    #[case(Some(rat("0"))         , "0")]
    #[case(Some(rat("1"))         , "1")]
    #[case(Some(rat("-1"))        , "-1")]
    #[case(Some(rat("147"))       , "147")]
    #[case(Some(rat("-147"))      , "-147")]
    #[case(Some(rat("0"))         , "-0")]
    #[case(Some(rat("0"))         , "0000")]
    #[case(Some(rat("147"))       , "000147")]
    #[case(Some(rat("-147"))      , "-000147")]
    #[case(Some(rat("0"))         , "-0000")]
    #[case(Some(rat("0"))         , "0.0")]
    #[case(Some(rat("1"))         , "1.0")]
    #[case(Some(rat("-1"))        , "-1.0")]
    #[case(Some(rat("13/10"))     , "1.3")]
    #[case(Some(rat("-13/10"))    , "-1.3")]
    #[case(Some(rat("0"))         , "0000.0000")]
    #[case(Some(rat("1"))         , "0001.0000")]
    #[case(Some(rat("-1"))        , "-0001.0000")]
    #[case(Some(rat("13/10"))     , "0001.3000")]
    #[case(Some(rat("-13/10"))    , "-0001.3000")]
    #[case(Some(rat("1"))         , "1.")]
    #[case(Some(rat("1/10"))      , ".1")]
    #[case(Some(rat("-3/10"))     , "-.3")]
    #[case(Some(rat("0"))         , ".0")]
    #[case(Some(rat("0"))         , "-.0")]
    #[case(Some(rat("0"))         , "0.")]
    #[case(Some(rat("0"))         , "-0.")]
    #[case(Some(rat("0"))         , "0/1")]
    #[case(Some(rat("1"))         , "1/1")]
    #[case(Some(rat("-1"))        , "-1/1")]
    #[case(Some(rat("1/2"))       , "1/2")]
    #[case(Some(rat("-1/2"))      , "-1/2")]
    #[case(Some(rat("0"))         , "0/123")]
    #[case(Some(rat("0"))         , "0/-123")]
    #[case(Some(rat("-1"))        , "1/-1")]
    #[case(Some(rat("1/2"))       , "1024/2048")]
    #[case(Some(rat("1/2"))       , "-1024/-2048")]
    #[case(Some(rat("-1/2"))      , "1/-2")]
    #[case(Some(rat("-1/2"))      , "-1024/2048")]
    #[case(Some(rat("1/2"))       , "0001024/0002048")]
    #[case(Some(rat("-1/2"))      , "-0001024/0002048")]
    #[case(Some(rat("1/2"))       , "1024 / 2048")]
    #[case(Some(rat("1/2"))       , "1024/ 2048")]
    #[case(Some(rat("1/2"))       , "1024 /2048")]
    #[case(Some(rat("1/2"))       , "1024   /   2048")]
    #[case(Some(rat("4"))         , "2/0.5")]
    #[case(Some(rat("1/4"))       , "0.5/2")]
    #[case(Some(rat("5/4"))       , "0.5/0.4")]
    #[case(Some(rat("5/4"))       , ".5/.4")]
    #[case(Some(rat("-1"))        , "\u{2212}1")]
    #[case(Some(rat("-1"))        , "\u{FF0D}1")]
    #[case(Some(rat("-1"))        , "-\u{FF11}")]
    #[case(Some(rat("5/4"))       , "5./4.")]
    #[case(Some(rat("5/4"))       , "5\u{2044}4")]
    #[case(Some(rat("0"))         , "0e0")]
    #[case(Some(rat("0"))         , "-0e0")]
    #[case(Some(rat("1"))         , "1e0")]
    #[case(Some(rat("1"))         , "1e-0")]
    #[case(Some(rat("0"))         , "0e-0")]
    #[case(Some(rat("-1"))        , "-1e0")]
    #[case(Some(rat("1"))         , "1.0e0")]
    #[case(Some(rat("-1"))        , "-1.0e0")]
    #[case(Some(rat("0"))         , "0e4")]
    #[case(Some(rat("0"))         , "0e-4")]
    #[case(Some(rat("10000"))     , "1e4")]
    #[case(Some(rat("1/10000"))   , "1e-4")]
    #[case(Some(rat("-10000"))    , "-1e4")]
    #[case(Some(rat("-1/10000"))  , "-1e-4")]
    #[case(Some(rat("9/8"))       , "1.125e0")]
    #[case(Some(rat("90/8"))      , "1.125e1")]
    #[case(Some(rat("900/8"))     , "1.125e2")]
    #[case(Some(rat("9000/8"))    , "1.125e3")]
    #[case(Some(rat("90000/8"))   , "1.125e4")]
    #[case(Some(rat("9/8"))       , "1.125e0")]
    #[case(Some(rat("9/80"))      , "1.125e-1")]
    #[case(Some(rat("9/800"))     , "1.125e-2")]
    #[case(Some(rat("9/8000"))    , "1.125e-3")]
    #[case(Some(rat("9/80000"))   , "1.125e-4")]
    #[case(Some(rat("9/8000"))    , "1.125E-3")]
    #[case(Some(rat("10000"))     , "1.e4")]
    #[case(Some(rat("1000"))      , ".1e4")]
    #[case(Some(rat("100000"))    , "10e4")]
    #[case(Some(rat("7/10"))      , "7/1e1")]
    #[case(Some(rat("7/100"))     , "0.7/1e1")]
    #[case(Some(rat("7/100"))     , "7e-1/1e1")]
    #[case(Some(rat("7/100"))     , "7e-1   /   1e1")]
    #[case(Some(rat("0"))         , "-(0/1)")]
    #[case(Some(rat("-1"))        , "-(1/1)")]
    #[case(Some(rat("1"))         , "-(-1/1)")]
    #[case(Some(rat("-1/2"))      , "-(1/2)")]
    #[case(Some(rat("1/2"))       , "-(-1/2)")]
    #[case(None                   , "")]
    #[case(None                   , "-")]
    #[case(None                   , ".")]
    #[case(None                   , "-.")]
    #[case(None                   , "1.-3")]
    #[case(None                   , "3/")]
    #[case(None                   , "/4")]
    #[case(None                   , "--1")]
    #[case(None                   , "1-1")]
    #[case(None                   , "1.3-1")]
    #[case(None                   , "e")]
    #[case(None                   , "-e1")]
    #[case(None                   , "2e-")]
    #[case(None                   , "-e-")]
    #[case(Some(rat("100000000")) , "100 000 000")]
    #[case(Some(rat("9/8000"))    , "1\u{2C}125E-3")]
    #[case(Some(pi("1"))          , "π")]
    #[case(Some(pi("1"))          , "pi")]
    #[case(Some(pi("1"))          , "1π")]
    #[case(Some(pi("1"))          , "1 π")]
    #[case(Some(pi("1"))          , "1   π")]
    #[case(Some(rat("0"))         , "0π")]
    #[case(Some(rat("0"))         , "0.0π")]
    #[case(Some(pi("2"))          , "2π")]
    #[case(Some(pi("-1"))         , "-1π")]
    #[case(Some(pi("3/2"))        , "1.5π")]
    #[case(Some(pi("-3/2"))       , "-1.5π")]
    #[case(Some(pi("1"))          , "π/1")]
    #[case(Some(pi("1"))          , "1π/1")]
    #[case(Some(pi("1"))          , "2π/2")]
    #[case(Some(pi("2"))          , "2π/1")]
    #[case(Some(pi("1/2"))        , "π/2")]
    #[case(Some(pi("3/2"))        , "3π/2")]
    #[case(Some(pi("3/2"))        , "3   π   /   2")]
    #[case(Some(pi("3/2"))        , "3   pi   /   2")]
    #[case(Some(rat("0"))         , "0e1π")]
    #[case(Some(pi("10"))         , "1e1π")]
    #[case(Some(pi("1500"))       , "1.5e3π")]
    #[case(Some(pi("3/100"))      , "3e-2   pi")]
    #[case(Some(pi("3000/2"))     , "3e3π/2")]
    #[case(Some(pi("3000000/2"))  , "3e3π/2e-3")]
    #[case(Some(pi("3000000/2"))  , "(3e3/2e-3)π")]
    #[case(Some(pi("3000000/2"))  , "π(3e3/2e-3)")]
    #[case(Some(pi("1500"))       , "π(1.5e3)")]
    #[case(Some(pi("1500"))       , "π   (1.5e3)")]
    #[case(Some(pi("3000000/2"))  , "(3e3  /  2e-3)  π ")]
    #[case(Some(pi("3000000/2"))  , "π  (3e3  /  2e-3) ")]
    #[case(Some(pi("-1"))         , "-π")]
    #[case(Some(pi("-3000/2"))    , "-3e3π/2")]
    #[case(Some(pi("-3000000/2")) , "3e3π/-2e-3")]
    #[case(Some(pi("-3000000/2")) , "-(3e3/2e-3)π")]
    #[case(Some(pi("-3000000/2")) , "-π(3e3/2e-3)")]
    #[case(Some(pi("-1500"))      , "-π(1.5e3)")]
    #[case(Some(pi("-3000000/2")) , "- (3e3 / 2e-3) π")]
    #[case(Some(pi("-3000000/2")) , "-π (3e3 / 2e-3)")]
    #[case(Some(pi("-1500"))      , "-π (1.5e3)")]
    #[case(Some(pi("1/60"))       , "pi/60")]
    #[case(Some(rpi("1"))         , "1/π")]
    #[case(Some(rpi("-1"))        , "-1/π")]
    #[case(Some(rpi("-1"))        , "1/-π")]
    #[case(Some(rpi("100/3"))     , "1/3e-2π")]
    #[case(Some(rpi("5"))         , "5/π")]
    #[case(Some(rpi("5/3"))       , "5/3π")]
    #[case(Some(rpi("87/100"))    , "0.87/π")]
    #[case(Some(rpi("87/100"))    , "0.87/pi")]
    #[case(Some(rpi("-5/3"))      , "-5/3π")]
    #[case(Some(rpi("-5/3"))      , "5/-3π")]
    #[case(Some(rpi("5/3"))       , "-5/-3π")]
    #[case(Some(rpi("-5"))        , "-5/π")]
    #[case(Some(rpi("-5"))        , "5/-π")]
    #[case(Some(rpi("5"))         , "-5/-π")]
    #[case(Some(rpi("5"))         , "5   /   π")]
    #[case(Some(rpi("-5"))        , "5   /   -π")]
    #[case(Some(rpi("-5"))        , "-5   /   π")]
    #[case(Some(rpi("5"))         , "-5   /   -π")]
    #[case(Some(rpi("5/3"))       , "5   /   3   π")]
    #[case(Some(rpi("-5/3"))      , "-5   /   3   π")]
    #[case(Some(rpi("-5/3"))      , "5   /   -3   π")]
    #[trace]
    fn test_parse(#[case] expected: Option<Number>, #[case] string: &str) {
        let actual = string.parse::<Number>();

        match (expected, actual) {
            (None, Err(_)) => {
                // Pass.
            },
            (None, Ok(actual)) => {
                panic!("Expected error\nActual: {}", actual);
            },
            (Some(expected), Err(error)) => {
                panic!("Expected: {}\nError: {}", expected, error);
            },
            (Some(expected), Ok(actual)) => {
                assert_eq!(expected, actual);
            },
        }
    }

    // Tests negation of numbers.
    test_operation_unary!(test_negation, neg, neg, neg_mut,
        #[rstest]
        #[case(Some(rat("-1")) , rat("1"))]
        #[case(Some(pi("-1"))  , pi("1"))]
        #[case(Some(rpi("-1")) , rpi("1"))]
        #[case(Some(i(-1.0))   , i(1.0))]
        #[case(Some(rat("0"))  , rat("0"))]
        #[case(Some(i(0.0))    , i(0.0))]
        #[trace]
    );

    // Tests reciprocation of numbers.
    test_operation_unary!(test_reciprocation, recip, recip_ref, recip_mut,
        #[rstest]
        #[case(Some(rat("3/2"))           , rat("2/3"))]
        #[case(Some(rpi("3/2"))           , pi("2/3"))]
        #[case(Some(pi("3/2"))            , rpi("2/3"))]
        #[case(Some(i(3.0/2.0))           , i(2.0/3.0))]
        #[case(None                       , rat("0"))]
        #[case(Some(i(f64::INFINITY))     , i(0.0))]
        #[case(Some(i(f64::NEG_INFINITY)) , i(-0.0))]
        #[trace]
    );

    // Tests addition of numbers.
    test_operation_binary!(test_addition, add, add_assign,
        #[rstest]
        #[case(Some(rat("3"))           , rat("1") , rat("2"))]
        #[case(Some(i(1.0 + 2.0*PI))    , rat("1") , pi("2"))]
        #[case(Some(i(1.0 + 2.0/PI))    , rat("1") , rpi("2"))]
        #[case(Some(i(3.0))             , rat("1") , i(2.0))]
        #[case(Some(i(PI + 2.0))        , pi("1")  , rat("2"))]
        #[case(Some(pi("3"))            , pi("1")  , pi("2"))]
        #[case(Some(i(PI + 2.0/PI))     , pi("1")  , rpi("2"))]
        #[case(Some(i(PI + 2.0))        , pi("1")  , i(2.0))]
        #[case(Some(i(1.0/PI + 2.0))    , rpi("1") , rat("2"))]
        #[case(Some(i(1.0/PI + 2.0*PI)) , rpi("1") , pi("2"))]
        #[case(Some(rpi("3"))           , rpi("1") , rpi("2"))]
        #[case(Some(i(1.0/PI + 2.0))    , rpi("1") , i(2.0))]
        #[case(Some(i(3.0))             , i(1.0)   , rat("2"))]
        #[case(Some(i(1.0 + 2.0*PI))    , i(1.0)   , pi("2"))]
        #[case(Some(i(1.0 + 2.0/PI))    , i(1.0)   , rpi("2"))]
        #[case(Some(i(3.0))             , i(1.0)   , i(2.0))]
        #[case(Some(rat("0"))           , rat("1") , rat("-1"))]
        #[case(Some(rat("0"))           , pi("1")  , pi("-1"))]
        #[case(Some(rat("0"))           , rpi("1") , rpi("-1"))]
        #[case(Some(i(0.0))             , i(1.0)   , i(-1.0))]
        #[case(Some(i(0.0))             , rat("1") , i(-1.0))]
        #[case(Some(i(0.0))             , i(1.0)   , rat("-1"))]
        #[case(Some(rat("2"))           , rat("0") , rat("2"))]
        #[case(Some(pi("2"))            , rat("0") , pi("2"))]
        #[case(Some(rpi("2"))           , rat("0") , rpi("2"))]
        #[case(Some(i(2.0))             , rat("0") , i(2.0))]
        #[case(Some(i(2.0))             , i(0.0)   , rat("2"))]
        #[case(Some(i(2.0*PI))          , i(0.0)   , pi("2"))]
        #[case(Some(i(2.0/PI))          , i(0.0)   , rpi("2"))]
        #[case(Some(i(2.0))             , i(0.0)   , i(2.0))]
        #[case(Some(rat("1"))           , rat("1") , rat("0"))]
        #[case(Some(i(1.0))             , rat("1") , i(0.0))]
        #[case(Some(pi("1"))            , pi("1")  , rat("0"))]
        #[case(Some(i(PI))              , pi("1")  , i(0.0))]
        #[case(Some(rpi("1"))           , rpi("1") , rat("0"))]
        #[case(Some(i(1.0/PI))          , rpi("1") , i(0.0))]
        #[case(Some(i(1.0))             , i(1.0)   , rat("0"))]
        #[case(Some(i(1.0))             , i(1.0)   , i(0.0))]
        #[trace]
    );

    // Tests subtraction of numbers.
    test_operation_binary!(test_subtraction, sub, sub_assign,
        #[rstest]
        #[case(Some(rat("-1"))          , rat("1") , rat("2"))]
        #[case(Some(i(1.0 - 2.0*PI))    , rat("1") , pi("2"))]
        #[case(Some(i(1.0 - 2.0/PI))    , rat("1") , rpi("2"))]
        #[case(Some(i(-1.0))            , rat("1") , i(2.0))]
        #[case(Some(i(PI - 2.0))        , pi("1")  , rat("2"))]
        #[case(Some(pi("-1"))           , pi("1")  , pi("2"))]
        #[case(Some(i(PI - 2.0/PI))     , pi("1")  , rpi("2"))]
        #[case(Some(i(PI - 2.0))        , pi("1")  , i(2.0))]
        #[case(Some(i(1.0/PI - 2.0))    , rpi("1") , rat("2"))]
        #[case(Some(i(1.0/PI - 2.0*PI)) , rpi("1") , pi("2"))]
        #[case(Some(rpi("-1"))          , rpi("1") , rpi("2"))]
        #[case(Some(i(1.0/PI - 2.0))    , rpi("1") , i(2.0))]
        #[case(Some(i(-1.0))            , i(1.0)   , rat("2"))]
        #[case(Some(i(1.0 - 2.0*PI))    , i(1.0)   , pi("2"))]
        #[case(Some(i(1.0 - 2.0/PI))    , i(1.0)   , rpi("2"))]
        #[case(Some(i(-1.0))            , i(1.0)   , i(2.0))]
        #[case(Some(rat("0"))           , rat("1") , rat("1"))]
        #[case(Some(rat("0"))           , pi("1")  , pi("1"))]
        #[case(Some(rat("0"))           , rpi("1") , rpi("1"))]
        #[case(Some(i(0.0))             , i(1.0)   , i(1.0))]
        #[case(Some(i(0.0))             , rat("1") , i(1.0))]
        #[case(Some(i(0.0))             , i(1.0)   , rat("1"))]
        #[case(Some(rat("-2"))          , rat("0") , rat("2"))]
        #[case(Some(pi("-2"))           , rat("0") , pi("2"))]
        #[case(Some(rpi("-2"))          , rat("0") , rpi("2"))]
        #[case(Some(i(-2.0))            , rat("0") , i(2.0))]
        #[case(Some(i(-2.0))            , i(0.0)   , rat("2"))]
        #[case(Some(i(-2.0*PI))         , i(0.0)   , pi("2"))]
        #[case(Some(i(-2.0/PI))         , i(0.0)   , rpi("2"))]
        #[case(Some(i(-2.0))            , i(0.0)   , i(2.0))]
        #[case(Some(rat("1"))           , rat("1") , rat("0"))]
        #[case(Some(i(1.0))             , rat("1") , i(0.0))]
        #[case(Some(pi("1"))            , pi("1")  , rat("0"))]
        #[case(Some(i(PI))              , pi("1")  , i(0.0))]
        #[case(Some(rpi("1"))           , rpi("1") , rat("0"))]
        #[case(Some(i(1.0/PI))          , rpi("1") , i(0.0))]
        #[case(Some(i(1.0))             , i(1.0)   , rat("0"))]
        #[case(Some(i(1.0))             , i(1.0)   , i(0.0))]
        #[trace]
    );

    // Tests multiplication of numbers.
    test_operation_binary!(test_multiplication, mul, mul_assign,
        #[rstest]
        #[case(Some(rat("6"))           , rat("2") , rat("3"))]
        #[case(Some(pi("6"))            , rat("2") , pi("3"))]
        #[case(Some(rpi("6"))           , rat("2") , rpi("3"))]
        #[case(Some(i(6.0))             , rat("2") , i(3.0))]
        #[case(Some(pi("6"))            , pi("2")  , rat("3"))]
        #[case(Some(i(2.0*PI * 3.0*PI)) , pi("2")  , pi("3"))]
        #[case(Some(rat("6"))           , pi("2")  , rpi("3"))]
        #[case(Some(i(2.0*PI * 3.0))    , pi("2")  , i(3.0))]
        #[case(Some(rpi("6"))           , rpi("2") , rat("3"))]
        #[case(Some(rat("6"))           , rpi("2") , pi("3"))]
        #[case(Some(i(2.0/PI * 3.0/PI)) , rpi("2") , rpi("3"))]
        #[case(Some(i((2.0/PI) * 3.0))  , rpi("2") , i(3.0))]
        #[case(Some(i(6.0))             , i(2.0)   , rat("3"))]
        #[case(Some(i(2.0 * 3.0*PI))    , i(2.0)   , pi("3"))]
        #[case(Some(i(2.0 * (3.0/PI)))  , i(2.0)   , rpi("3"))]
        #[case(Some(i(6.0))             , i(2.0)   , i(3.0))]
        #[case(Some(rat("0"))           , rat("0") , rat("3"))]
        #[case(Some(rat("0"))           , rat("0") , pi("3"))]
        #[case(Some(rat("0"))           , rat("0") , rpi("3"))]
        #[case(Some(rat("0"))           , rat("0") , i(3.0))]
        #[case(Some(i(0.0))             , i(0.0)   , rat("3"))]
        #[case(Some(i(0.0))             , i(0.0)   , pi("3"))]
        #[case(Some(i(0.0))             , i(0.0)   , rpi("3"))]
        #[case(Some(i(0.0))             , i(0.0)   , i(3.0))]
        #[case(Some(rat("0"))           , rat("2") , rat("0"))]
        #[case(Some(i(0.0))             , rat("2") , i(0.0))]
        #[case(Some(rat("0"))           , pi("2")  , rat("0"))]
        #[case(Some(i(0.0))             , pi("2")  , i(0.0))]
        #[case(Some(rat("0"))           , rpi("2") , rat("0"))]
        #[case(Some(i(0.0))             , rpi("2") , i(0.0))]
        #[case(Some(rat("0"))           , i(2.0)   , rat("0"))]
        #[case(Some(i(0.0))             , i(2.0)   , i(0.0))]
        #[trace]
    );

    // Tests division of numbers.
    test_operation_binary!(test_division, div, div_assign,
        #[rstest]
        #[case(Some(rat("2/3"))             , rat("2") , rat("3"))]
        #[case(Some(rpi("2/3"))             , rat("2") , pi("3"))]
        #[case(Some(pi("2/3"))              , rat("2") , rpi("3"))]
        #[case(Some(i(2.0/3.0))             , rat("2") , i(3.0))]
        #[case(Some(pi("2/3"))              , pi("2")  , rat("3"))]
        #[case(Some(rat("2/3"))             , pi("2")  , pi("3"))]
        #[case(Some(i((2.0*PI) / (3.0/PI))) , pi("2")  , rpi("3"))]
        #[case(Some(i((2.0*PI) / 3.0))      , pi("2")  , i(3.0))]
        #[case(Some(rpi("2/3"))             , rpi("2") , rat("3"))]
        #[case(Some(i((2.0/PI) / (3.0*PI))) , rpi("2") , pi("3"))]
        #[case(Some(rat("2/3"))             , rpi("2") , rpi("3"))]
        #[case(Some(i((2.0/PI) / 3.0))      , rpi("2") , i(3.0))]
        #[case(Some(i(2.0/3.0))             , i(2.0)   , rat("3"))]
        #[case(Some(i(2.0 / (3.0*PI)))      , i(2.0)   , pi("3"))]
        #[case(Some(i(2.0 / (3.0/PI)))      , i(2.0)   , rpi("3"))]
        #[case(Some(i(2.0/3.0))             , i(2.0)   , i(3.0))]
        #[case(Some(rat("0"))               , rat("0") , rat("3"))]
        #[case(Some(rat("0"))               , rat("0") , pi("3"))]
        #[case(Some(rat("0"))               , rat("0") , rpi("3"))]
        #[case(Some(rat("0"))               , rat("0") , i(3.0))]
        #[case(Some(i(0.0))                 , i(0.0)   , rat("3"))]
        #[case(Some(i(0.0))                 , i(0.0)   , pi("3"))]
        #[case(Some(i(0.0))                 , i(0.0)   , rpi("3"))]
        #[case(Some(i(0.0))                 , i(0.0)   , i(3.0))]
        #[case(None                         , rat("2") , rat("0"))]
        #[case(Some(i(f64::INFINITY))       , rat("2") , i(0.0))]
        #[case(None                         , pi("2")  , rat("0"))]
        #[case(Some(i(f64::INFINITY))       , pi("2")  , i(0.0))]
        #[case(None                         , rpi("2") , rat("0"))]
        #[case(Some(i(f64::INFINITY))       , rpi("2") , i(0.0))]
        #[case(None                         , i(2.0)   , rat("0"))]
        #[case(Some(i(f64::INFINITY))       , i(2.0)   , i(0.0))]
        #[trace]
    );

    // Tests exponentiation of numbers.
    #[rstest]
    #[case(Some(rat("4"))         , rat("2") , 2)]
    #[case(Some(i(4.0*PI.pow(2))) , pi("2")  , 2)]
    #[case(Some(i(4.0/PI.pow(2))) , rpi("2") , 2)]
    #[case(Some(i(4.0))           , i(2.0)   , 2)]
    #[case(Some(rat("0"))         , rat("0") , 2)]
    #[case(Some(i(0.0))           , i(0.0)   , 2)]
    #[case(Some(rat("1"))         , i(2.0)   , 0)]
    #[case(Some(rat("1"))         , rat("0") , 0)]
    #[case(Some(rat("1"))         , i(0.0)   , 0)]
    #[trace]
    fn test_exponentiation(
        #[case] expected: Option<Number>,
        #[case] operand_left: Number,
        #[case] operand_right: i32
    ) {
        // Owned operand.
        assert_number_eq(&expected, || {
            operand_left.clone().pow(operand_right)
        });

        // Immutable reference operand.
        assert_number_eq(&expected, || {
            (&operand_left).pow_ref(operand_right)
        });

        // Mutable reference operand.
        assert_number_eq(&expected, || {
            let mut operand_left = operand_left.clone();
            operand_left.pow_mut(operand_right);
            operand_left
        });
    }



    // /// Tests formatting of magnitudes.
    // #[test_case(format!("{}", rat("0"))    => "0"     ; "display_1")]
    // #[test_case(format!("{}", rat("1"))    => "1"     ; "display_2")]
    // #[test_case(format!("{}", rat("-1"))   => "-1"    ; "display_3")]
    // #[test_case(format!("{}", rat("1/2"))  => "1/2"   ; "display_4")]
    // #[test_case(format!("{}", rat("-1/2")) => "-1/2"  ; "display_5")]
    // #[test_case(format!("{}", pi("1"))     => "π"     ; "display_6")]
    // #[test_case(format!("{}", pi("-1"))    => "-π"    ; "display_7")]
    // #[test_case(format!("{}", pi("1/2"))   => "π/2"   ; "display_8")]
    // #[test_case(format!("{}", pi("-1/2"))  => "-π/2"  ; "display_9")]
    // #[test_case(format!("{}", pi("3/2"))   => "3π/2"  ; "display_10")]
    // #[test_case(format!("{}", pi("-3/2"))  => "-3π/2" ; "display_11")]
    // #[test_case(format!("{}", rpi("1"))    => "1/π"   ; "display_12")]
    // #[test_case(format!("{}", rpi("-1"))   => "-1/π"  ; "display_13")]
    // #[test_case(format!("{}", rpi("1/2"))  => "1/2π"  ; "display_14")]
    // #[test_case(format!("{}", rpi("-1/2")) => "-1/2π" ; "display_15")]
    // #[test_case(format!("{}", rpi("3/2"))  => "3/2π"  ; "display_16")]
    // #[test_case(format!("{}", rpi("-3/2")) => "-3/2π" ; "display_17")]
    // // #[test_case(format!("{:e}", rat("0"))   => "0"      ; "scientific_1")]
    // // #[test_case(format!("{:e}", rat("1"))   => "1e0"    ; "scientific_2")]
    // // #[test_case(format!("{:e}", rat("-1"))  => "-1e0"   ; "scientific_3")]
    // // #[test_case(format!("{:e}", rat("1/2")) => "1.5e-1" ; "scientific_4")]
    // fn test_format(string: String) -> String {
    //     string
    // }






    




}