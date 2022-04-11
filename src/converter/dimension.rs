#[cfg(any(test, not(mainbuild)))] use anyhow::Error;
use serde::Deserialize;
use serde::Serialize;
#[cfg(any(test, not(mainbuild)))] use std::collections::HashMap;
use std::ops::Mul;
use std::ops::MulAssign;

/// A quantity dimension.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Dimension {
    data: [i8; Dimension::MAX_BASES],
}

impl Dimension {
    /// The maximum number of base dimensions.
    pub const MAX_BASES: usize = 32;

    /// Returns a dimensionless dimension.
    #[cfg(mainbuild)]
    pub fn dimensionless() -> Dimension {
        Dimension {data: [0; Dimension::MAX_BASES]}
    }

    /// Parses a dimension string according to some set of bases.
    #[cfg(any(test, not(mainbuild)))]
    pub fn parse(bases: &HashMap<String, usize>, string: &str)
    -> Result<Dimension, Error> {
        use anyhow::anyhow;
        use anyhow::ensure;

        // TODO might wanna check bases out for validity

        const DELIMITER_COMPONENT: char = '*';
        const DELIMITER_EXPONENT: char = '^';

        let mut data = [0; Dimension::MAX_BASES];

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

                ensure!(exponent != 0, "Illegal schema");
            }
            // Exponent is unspecified; implied to be 1.
            else {
                base = part;
                exponent = 1;
            }

            let base = bases.get(base).ok_or_else(||
                anyhow!("Unknown dimension")
            )?;

            data[*base] = exponent;
        }

        Ok(Dimension {data})
    }

    /// Assigns this dimension to its reciprocal.
    #[cfg(mainbuild)]
    pub fn recip_mut(&mut self) {
        for base in 0..Dimension::MAX_BASES {
            self.data[base] *= -1;
        }
    }

    /// Returns this dimension raised to some exponent.
    #[cfg(mainbuild)]
    pub fn pow(mut self, exponent: i8) -> Dimension {
        self.pow_mut(exponent);
        self
    }

    /// Assigns this dimension to itself raised to some exponent.
    #[cfg(mainbuild)]
    pub fn pow_mut(&mut self, exponent: i8) {
        for base in 0..Dimension::MAX_BASES {
            self.data[base] *= exponent;
        }
    }
}

/// Implements computation of multiplication over dimensions.
impl MulAssign<Dimension> for Dimension {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn mul_assign(&mut self, multiplicand: Dimension) {
        for base in 0..Dimension::MAX_BASES {
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
    use test_case::test_case;

    #[test_case("AAA" ,            vec![1, 0, 0]  ; "_1")]
    #[test_case("BBB" ,            vec![0, 1, 0]  ; "_2")]
    #[test_case("CCC" ,            vec![0, 0, 1]  ; "_3")]
    #[test_case("AAA*BBB" ,        vec![1, 1, 0]  ; "_4")]
    #[test_case("BBB*CCC" ,        vec![0, 1, 1]  ; "_5")]
    #[test_case("AAA*CCC" ,        vec![1, 0, 1]  ; "_6")]
    #[test_case("AAA*BBB*CCC" ,    vec![1, 1, 1]  ; "_7")]
    #[test_case("AAA^2*BBB*CCC" ,  vec![2, 1, 1]  ; "_8")]
    #[test_case("AAA*BBB^-2*CCC" , vec![1, -2, 1] ; "_9")]
    fn test_parse(string: &str, expected: Vec<i8>) {
        lazy_static! {
            static ref BASES: HashMap<String, usize> = hashmap![
                "AAA" => 0,
                "BBB" => 1,
                "CCC" => 2,
            ].into_iter().map(|(k, v)| (k.to_string(), v)).collect::<HashMap<_, _>>();
        }

        assert!(expected.len() <= Dimension::MAX_BASES);

        let mut data_expected = [0; Dimension::MAX_BASES];

        for (index, component) in expected.into_iter().enumerate() {
            data_expected[index] = component;
        }

        let expected = Dimension {data: data_expected};

        let actual = Dimension::parse(&BASES, string).unwrap();

        assert_eq!(actual, expected);
    }
}