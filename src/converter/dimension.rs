#[cfg(any(test, not(mainbuild)))] use anyhow::Error;
use serde::Deserialize;
use serde::Serialize;
#[cfg(any(test, not(mainbuild)))] use std::collections::HashMap;
#[cfg(any(test, not(mainbuild)))] use std::collections::HashSet;
use std::ops::Mul;
use std::ops::MulAssign;

/// A quantity dimension.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Dimension {
    data: [i8; Dimension::MAX_BASES],
}

impl Dimension {
    /// The maximum number of base dimensions.
    pub const MAX_BASES: usize = 8;

    /// Returns a dimensionless dimension.
    #[cfg(mainbuild)]
    pub fn dimensionless() -> Dimension {
        Dimension {data: [0; Dimension::MAX_BASES]}
    }

    /// Parses a dimension string according to some set of bases.
    #[cfg(any(test, not(mainbuild)))]
    pub fn parse(bases: &HashMap<&str, usize>, string: &str)
    -> Result<Dimension, Error> {
        use anyhow::anyhow;
        use anyhow::ensure;

        // TODO might wanna check bases out for validity

        const DELIMITER_COMPONENT: char = '*';
        const DELIMITER_EXPONENT: char = '^';

        let mut data = [0; Dimension::MAX_BASES];
        let mut bases_seen = HashSet::new();

        // Parse the dimension string.
        for part in string.split(DELIMITER_COMPONENT) {
            let base;
            let exponent;

            let part = part.trim();

            // Exponent is specified.
            if let Some((string_base, string_exponent))
            = part.split_once(DELIMITER_EXPONENT) {
                base = string_base;
                exponent = string_exponent.trim().parse::<i8>().map_err(|_|
                    anyhow!("Illegal dimension exponent")
                )?;

                ensure!(exponent != 0, "Illegal dimension exponent");
            }
            // Exponent is unspecified; implied to be 1.
            else {
                base = part;
                exponent = 1;
            }

            let base = bases.get(base).ok_or_else(||
                anyhow!("Unknown dimension base")
            )?;

            ensure!(!bases_seen.contains(base), "Duplicate dimension base");

            bases_seen.insert(base);

            data[*base] = exponent;
        }

        Ok(Dimension {data})
    }

    /// Returns the reciprocal of this dimension.
    #[cfg(mainbuild)]
    pub fn recip(mut self) -> Dimension {
        for base in 0..Dimension::MAX_BASES {
            self.data[base] *= -1;
        }

        self
    }

    /// Returns this dimension raised to some exponent.
    #[cfg(mainbuild)]
    pub fn pow(mut self, exponent: i8) -> Dimension {
        for base in 0..Dimension::MAX_BASES {
            // TODO use checked_mul
            self.data[base] *= exponent;
        }

        self
    }
}

/// Implements computation of multiplication over dimensions.
impl MulAssign<Dimension> for Dimension {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn mul_assign(&mut self, multiplicand: Dimension) {
        for base in 0..Dimension::MAX_BASES {
            // TODO use checked_add
            self.data[base] += multiplicand.data[base];
        }
    }
}

/// Implements computation of multiplication over dimensions.
impl Mul<Dimension> for Dimension {
    type Output = Dimension;

    fn mul(mut self, multiplicand: Dimension) -> Dimension {
        self *= multiplicand;
        self
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    use lazy_static::lazy_static;
    use maplit::hashmap;
    use rstest::rstest;

    /// Returns a dimension from a list of exponents.
    fn dimension(components: &[i8]) -> Dimension {
        let mut data = [0; Dimension::MAX_BASES];

        for (index, component) in components.iter().enumerate() {
            data[index] = *component;
        }

        Dimension {data}
    }

    #[rstest]
    #[case(vec![1 , 0  , 0] , "AAA")]
    #[case(vec![0 , 1  , 0] , "BBB")]
    #[case(vec![0 , 0  , 1] , "CCC")]
    #[case(vec![1 , 1  , 0] , "AAA*BBB")]
    #[case(vec![0 , 1  , 1] , "BBB*CCC")]
    #[case(vec![1 , 0  , 1] , "AAA*CCC")]
    #[case(vec![1 , 1  , 1] , "AAA*BBB*CCC")]
    #[case(vec![2 , 1  , 1] , "AAA^2*BBB*CCC")]
    #[case(vec![1 , -2 , 1] , "AAA*BBB^-2*CCC")]
    #[trace]
    fn test_parse(#[case] expected: Vec<i8>, #[case] string: &str) {
        lazy_static! {
            static ref BASES: HashMap<&'static str, usize> = hashmap![
                "AAA" => 0,
                "BBB" => 1,
                "CCC" => 2,
            ];
        }

        assert!(expected.len() <= Dimension::MAX_BASES);

        let expected = dimension(&expected);

        let actual = Dimension::parse(&BASES, string).unwrap();

        assert_eq!(expected, actual);
    }

    #[rstest]
    #[case(vec![-1 , -2 , -3] , vec![1 , 2 , 3])]
    #[case(vec![0  , 0  , 0]  , vec![0 , 0 , 0])]
    #[trace]
    fn test_reciprocation(
        #[case] expected: Vec<i8>,
        #[case] operand: Vec<i8>
    ) {
        let expected = dimension(&expected);
        let operand = dimension(&operand);

        let reciprocal = operand.recip();

        assert_eq!(expected, reciprocal);
    }

    #[rstest]
    #[case(vec![1 , 1 , 0] , vec![1 , 0 , 0] , vec![0  , 1 , 0])]
    #[case(vec![1 , 1 , 1] , vec![1 , 0 , 1] , vec![0  , 1 , 0])]
    #[case(vec![1 , 2 , 3] , vec![1 , 2 , 0] , vec![0  , 0 , 3])]
    #[case(vec![2 , 0 , 0] , vec![1 , 0 , 0] , vec![1  , 0 , 0])]
    #[case(vec![0 , 0 , 0] , vec![1 , 0 , 0] , vec![-1 , 0 , 0])]
    #[trace]
    fn test_multiplication(
        #[case] expected: Vec<i8>,
        #[case] multiplier: Vec<i8>,
        #[case] multiplicand: Vec<i8>
    ) {
        let expected = dimension(&expected);
        let multiplier = dimension(&multiplier);
        let multiplicand = dimension(&multiplicand);

        let product = multiplier * multiplicand;

        assert_eq!(expected, product);
    }

    #[rstest]
    #[case(vec![1  , 2  , 3]  , vec![1 , 2 , 3] , 1)]
    #[case(vec![0  , 0  , 0]  , vec![1 , 2 , 3] , 0)]
    #[case(vec![2  , 4  , 6]  , vec![1 , 2 , 3] , 2)]
    #[case(vec![-1 , -2 , -3] , vec![1 , 2 , 3] , -1)]
    #[case(vec![-2 , -4 , -6] , vec![1 , 2 , 3] , -2)]
    #[trace]
    fn test_exponentiation(
        #[case] expected: Vec<i8>,
        #[case] base: Vec<i8>,
        #[case] exponent: i8
    ) {
        let expected = dimension(&expected);
        let base = dimension(&base);

        let power = base.pow(exponent);

        assert_eq!(expected, power);
    }
}