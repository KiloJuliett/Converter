mod dimension;

use anyhow::anyhow;
use anyhow::bail;
use anyhow::ensure;
use anyhow::Error;
use lazy_static::lazy_static;
use regex::Regex;
use serde::Deserialize;
use serde::Serialize;
use std::collections::HashMap;
#[cfg(any(test, not(mainbuild)))] use std::path::Path;
use unicode_normalization::UnicodeNormalization;

use crate::converter::dimension::Dimension;
// use crate::handlers::HANDLERS_RELATIONS;
// use crate::handlers::HANDLERS_UNITS;
use crate::number::Number;

/// A unit converter.
/// 
/// This structure represents a unit converter. Unit converters can only be
/// created at compilation time (by a build script).
#[derive(Deserialize, Serialize)]
pub struct Converter {
    /// The named units in this converter, organized by their symbols and then
    /// their dimensions.
    units: HashMap<String, HashMap<Dimension, (Number, Number)>>,

    /// The aliases in this converter, organized by their symbols and then their
    /// dimensions.
    aliases: HashMap<String, HashMap<Dimension, String>>,

    // TODO relations
    // TODO designations
}

impl Converter {
    /// Parses the given database files and builds a unit converter.
    /// 
    /// This function reads the given files and parses it according to the rules
    /// of record files, building a unit converter and returning it.
    /// 
    /// This function is not available at runtime. This function is meant to
    /// only be run during compilation; therefore, it is not compiled into the
    /// main binary.
    #[cfg(any(test, not(mainbuild)))]
    pub fn build(paths: Vec<impl AsRef<Path>>) -> Result<Converter, Error> {
        use std::fs::File;
        use std::io::BufRead;
        use std::io::BufReader;
        use std::vec;

        const DELIMITER_COMMENT: char = '#';
        const DELIMITER_RECORD: char = '|';

        let mut records_bases = vec![];
        let mut records_prefixes = vec![];
        let mut records_units = vec![];
        let mut records_aliases = vec![];

        for path in paths.iter() {
            let path = path.as_ref();
            let file = File::open(path)?;

            for (line, number) in BufReader::new(file).lines().zip(1..) {
                let line = line?;
                let mut line = line.as_str();

                // Strip comments
                if let Some((record, _)) = line.split_once(DELIMITER_COMMENT) {
                    line = record;
                }

                // Strip whitespace.
                line = line.trim();

                // Skip empty lines
                if line.is_empty() {
                    continue;
                }

                // Split line into strings and strip whitespace some more.
                let mut record = line.split(DELIMITER_RECORD).map(|string_record| {
                    string_record.trim().to_string()
                });

                let type_record = record.next().unwrap();
                let record = record.collect::<Vec<String>>();

                // Sort the record.
                let records = match type_record.as_str() {
                    "B" => &mut records_bases,
                    "P" => &mut records_prefixes,
                    "U" => &mut records_units,
                    "A" => &mut records_aliases,

                    _ =>
                        bail!("{}:{}: Unknown record type", path.display(), number),
                };

                records.push((record, path, number));
            }
        }

        /// Processes records with a record processor.
        fn process_records(
            records: Vec<(Vec<String>, &Path, usize)>,
            mut processor: impl FnMut(Vec<String>) -> Result<(), Error>)
        -> Result<(), Error> {
            for (record, path, number) in records {
                processor(record).map_err(|error| {
                    anyhow!("{}:{}: {}", path.display(), number, error)
                })?
            }

            Ok(())
        }

        /// Converts the given record into an array for unboxing.
        fn into_array<const N: usize>(record: Vec<String>)
        -> Result<[String; N], Error> {
            match record.try_into() {
                Ok(record) => Ok(record),
                Err(_) => bail!("Illegal argument count")
            }
        }

        let mut bases = HashMap::new();
        let mut prefixes = HashMap::new();
        let mut units = HashMap::new();
        let mut aliases = HashMap::new();

        // Insert the "identity prefix."
        prefixes.insert(String::new(), Number::one_exact());

        // Process base dimensions (B-records).
        process_records(records_bases, |record| {
            lazy_static! {
                static ref REGEX: Regex = Regex::new(r"^[A-Z]{3}$").unwrap();
            }

            let [string_base] = into_array(record)?;

            ensure!(REGEX.is_match(&string_base), "Illegal base dimension");
            ensure!(bases.len() < Dimension::MAX_BASES, "More than {} base dimensions are unsupported", Dimension::MAX_BASES);

            // Assign a unique sequential ID to the base.
            if bases.insert(string_base, bases.len()).is_some() {
                bail!("Duplicate base dimension");
            }

            Ok(())
        })?;

        // TODO R

        // Process prefixes for named units (P-records).
        process_records(records_prefixes, |record| {
            lazy_static! {
                static ref REGEX: Regex = Regex::new(r"^\w+$").unwrap();
            }

            let [prefix, magnitude] = into_array(record)?;

            ensure!(REGEX.is_match(&prefix), "Illegal prefix");

            let magnitude = magnitude.parse::<Number>()?;

            // TODO Are negative magnitudes sensible?
            ensure!(magnitude != Number::zero_exact(), "Illegal prefix magnitude");

            if prefixes.insert(prefix, magnitude).is_some() {
                bail!("Duplicate prefix");
            }

            Ok(())
        })?;

        // Process named units (U-records).
        process_records(records_units, |record| {
            const DELIMITER_AFFINE: char = '+';

            let [symbol, string_dimension, transformation] = into_array(record)?;

            // TODO validate symbol

            // And then the LORD said, "Let symbols be canonicalized according
            // to the semantics of NFKC normalization:" and it was so.
            let symbol = symbol.nfkc().collect::<String>();

            let dimension = Dimension::parse(&bases, string_dimension.as_str())?;

            let magnitude;
            let offset;

            // Magnitude and offset specified
            if let Some((string_magnitude, string_offset))
            = transformation.split_once(DELIMITER_AFFINE) {
                magnitude = string_magnitude.parse::<Number>()?;
                offset = string_offset.parse::<Number>()?;
            }
            // Only magnitude specified
            else {
                magnitude = transformation.parse::<Number>()?;
                offset = Number::zero_exact();
            }

            // Generate prefixed units.
            for (prefix, magnitude_prefix) in prefixes.iter() {
                let symbol_prefixed = format!("{}{}", prefix, symbol);
                let magnitude_prefixed = &magnitude * magnitude_prefix;

                if units.entry(symbol_prefixed).or_insert_with(HashMap::new)
                .insert(dimension, (magnitude_prefixed, offset.clone()))
                .is_some() {
                    bail!("Duplicate unit");
                }
            }

            Ok(())
        })?;

        // Process aliases (A-records).
        process_records(records_aliases, |record| {
            let [symbol_alias, symbol_aliasee, string_dimension] = into_array(record)?;

            // TODO validate symbols

            let dimension = Dimension::parse(&bases, string_dimension.as_str())?;

            // Generate prefixed aliases.
            for (prefix, _) in prefixes.iter() {
                let symbol_alias_prefixed = format!("{}{}", prefix, symbol_alias);
                let symbol_aliasee_prefixed = format!("{}{}", prefix, symbol_aliasee);

                if aliases.entry(symbol_alias_prefixed).or_insert_with(HashMap::new)
                .insert(dimension, symbol_aliasee_prefixed).is_some() {
                    bail!("Duplicate alias");
                }
            }

            Ok(())
        })?;

        Ok(Converter {units, aliases})
    }

    /// Returns a new unit converter.
    #[cfg(mainbuild)]
    pub fn new() -> Converter {
        const DATA_CONVERTER: &[u8] = include_bytes!(env!("PATH_DATA_CONVERTER"));

        bincode::deserialize::<Converter>(DATA_CONVERTER).unwrap()
    }

    /// Performs a unit conversion.
    #[cfg(mainbuild)]
    pub fn convert(
        &self,
        symbol_source: &str,
        symbol_destination: &str,
        magnitude: &Number
    ) -> Result<Number, Error> {
        // Returns the possible "interpretations" of the given symbol.
        let interpretations = |symbol: &str|
        -> Result<HashMap<Dimension, (Number, Number)>, Error> {
            lazy_static! {
                static ref REGEX_INTEGER: Regex = Regex::new(
                    r"(?:-|\u{2212})?\d+" // TODO what character indicates negation?
                ).unwrap();
                static ref REGEX_POSITIVEINTEGER: Regex = Regex::new(
                    r"^\d+"
                ).unwrap();
                static ref REGEX_MULTIPLICATION: Regex = Regex::new(
                    r"[\u{22C5}\u{00B7}\*]" // TODO unicode hyphens?
                ).unwrap();
                static ref REGEX_DIVISION: Regex = Regex::new(
                    r"[/\u{2044}\u{2215}]"
                ).unwrap();
                static ref REGEX_EXPONENTIATION: Regex = Regex::new(
                    r"\^"
                ).unwrap();
            }
    
            let terms_division = REGEX_DIVISION.split(symbol)
            .map(str::trim)
            .collect::<Vec<&str>>();
    
            ensure!((1..=2).contains(&terms_division.len()), "Illegal symbol");
    
            /// Parses the given component string and returns its components.
            fn parse_components(string: &str) -> Result<Vec<(&str, i8)>, Error> {
                let mut components = Vec::new();
    
                let terms_multiplication = REGEX_MULTIPLICATION.split(string)
                .map(str::trim)
                .collect::<Vec<&str>>();
    
                for term_multiplication in terms_multiplication.iter() {
                    let mut terms_exponentiation
                    = REGEX_EXPONENTIATION.split(term_multiplication)
                    .map(str::trim);
    
                    let base = terms_exponentiation.next().unwrap();
    
                    // TODO validate symbol
                    ensure!(!base.is_empty(), "Illegal symbol");
    
                    let exponent
                    = if let Some(string_power) = terms_exponentiation.next() {
                        ensure!(REGEX_INTEGER.is_match(string_power), "Illegal symbol {}", string_power);
    
                        string_power.parse::<i8>().map_err(|_|
                            anyhow!("Exponents outside [-128, 127] are unsupported")
                        )?
                    } else {
                        1
                    };
    
                    // TODO is this a good thing to check?
                    ensure!(exponent != 0, "Illegal component exponent");
    
                    if terms_exponentiation.next().is_some() {
                        bail!("Illegal symbol");
                    }
    
                    components.push((base, exponent));
                }
    
                Ok(components)
            }

            // let mut components = Vec::new();
            let mut magnitude = Number::one_exact();

            // Handle numerator.
            let mut components = parse_components(terms_division[0])?;

            // Handle denominator.
            if terms_division.len() == 2 {
                let mut term_denominator = terms_division[1];

                if let Some(match_coefficient)
                = REGEX_POSITIVEINTEGER.find(term_denominator) {
                    magnitude /= match_coefficient.as_str().parse::<Number>()?;

                    term_denominator = &term_denominator[match_coefficient.end()..];
                }

                for (base, exponent) in parse_components(term_denominator)? {
                    components.push((base, -exponent));
                }
            }

            let mut components = components.into_iter();
    
            let mut interpretations = HashMap::new();
    
            // Special handling is required for the first component to correctly
            // handle offsets for named units.
            let (base, exponent) = components.next().unwrap();
            
            for (dimension_base, (magnitude_base, offset_base))
            in self.units.get(base).ok_or_else(|| anyhow!("Unknown component"))? {
                interpretations.insert(
                    dimension_base.pow(exponent),
                    (
                        &magnitude * magnitude_base.pow_ref(exponent as i32),
                        if exponent == 1 {offset_base.clone()} else {Number::zero_exact()}
                    )
                );
            }
    
            for (base, exponent) in components {
                let mut interpretations_new = HashMap::new();
    
                for (dimension_base, (magnitude_base, _))
                in self.units.get(base).ok_or_else(|| anyhow!("Unknown component"))? {
                    for (
                        dimension_interpretation,
                        (magnitude_interpretation, _)
                    ) in &interpretations {
                        interpretations_new.insert(
                            *dimension_interpretation * dimension_base.pow(exponent),
                            (
                                magnitude_interpretation * magnitude_base.pow_ref(exponent as i32),
                                Number::zero_exact()
                            )
                        );
                    }
                }
    
                interpretations = interpretations_new;
            }
    
            Ok(interpretations)
        };

        // Destroy the forces of evil with my magical Unicode powers.
        let symbol_source = symbol_source.nfkc().collect::<String>();
        let symbol_destination = symbol_destination.nfkc().collect::<String>();

        let interpretations_source = interpretations(symbol_source.as_str())?;

        let mut interpretations_destination = HashMap::new();
        
        // Include the reciprocal of every destination interpretation.
        for (mut dimension, transformation)
        in interpretations(symbol_destination.as_str())? {
            // Adds an destination interpretation.
            let mut add = |
                dimension: Dimension,
                transformation: (bool, (Number, Number))
            | -> Result<(), Error> {
                if let Some(transformation_present)
                = interpretations_destination.insert(dimension, transformation.clone()) {
                    if transformation != transformation_present {
                        // An interpretation with this dimension exists, and its
                        // transformation conflicts with this one.
                        bail!("Ambiguous conversion: {:?}, {:?}", transformation_present, transformation);
                    }
                }

                Ok(())
            };

            add(dimension, (false, transformation.clone()))?;

            // Add the reciprocal dimension (assuming it isn't dimensionless).
            if dimension != Dimension::dimensionless() {
                // dimension.recip_mut();

                dimension = dimension.recip();

                add(dimension, (true, transformation))?;
            }
        }

        let mut conversion = None;

        // Identify all possible ways the specified units can be converted.
        for (dimension, (magnitude_source, offset_source))
        in interpretations_source {
            if let Some((reciprocal, (magnitude_destination, offset_destination)))
            = interpretations_destination.get(&dimension) {
                let mut conversion_current = magnitude.clone();

                // Convert to reference.
                conversion_current *= magnitude_source;
                conversion_current += offset_source;
        
                // Convert between references (if necessary).
                if *reciprocal {
                    conversion_current.recip_mut();
                }
        
                // Convert from reference.
                conversion_current -= offset_destination;
                conversion_current /= magnitude_destination;

                // TODO some ambiguity can result if source magnitude is 0 (all
                // conversions will be 0, which in the current version of this
                // algorithm, implies that the conversion is always valid).

                // A conversion over this dimension exists, and it conflicts
                // with this one.
                if let Some(conversion_present) = &conversion {
                    ensure!(conversion_present == &conversion_current, "Ambiguous conversion:\n{:?}\n{:?}\n{:?}", dimension, conversion_present, conversion_current);
                }
                else {
                    conversion = Some(conversion_current);
                }
            }
        }

        ensure!(conversion.is_some(), "Units do not share dimension");

        Ok(conversion.unwrap())
    }
}



/// The converter `impl`, despite only being a couple hundred lines, has to
/// correctly handle tons of bizarre and often inconsistent edge cases, so as
/// you can imagine, it comes with an extremely large battery of tests. And in
/// case you were wondering, the vast majority of the not exactly supersonic
/// compilation time comes from the evaluation of all the macros here.
#[cfg(test)]
mod tests {
    use super::*;

    use rstest::rstest;
    use std::io::Write;
    use tempfile::NamedTempFile;

    /// Asserts that the given converter correctly converts.
    macro_rules! assert_converter {
        (
            $converter:expr,
            $expected:expr,
            $symbol_source:expr,
            $symbol_destination:expr,
            $magnitude_source:expr
        ) => {
            let magnitude_source = $magnitude_source.parse::<Number>().unwrap();

            let result
            = $converter.convert(
                $symbol_source,
                $symbol_destination,
                &magnitude_source
            );

            match ($expected, result) {
                (None, Err(_)) => {
                    // Pass.
                },
                (None, Ok(_)) => {
                    panic!("Expected failed conversion");
                },
                (Some(_), Err(error)) => {
                    panic!("Conversion failed: {:?}", error);
                },
                (Some(magnitude_expected), Ok(magnitude_destination)) => {
                    let magnitude_expected = magnitude_expected.parse::<Number>().unwrap();

                    assert_eq!(magnitude_expected, magnitude_destination);

                    let magnitude_destination_reverse
                    = $converter.convert(
                        $symbol_destination,
                        $symbol_source,
                        &magnitude_destination
                    ).unwrap();

                    assert_eq!(magnitude_source, magnitude_destination_reverse);
                }
            }
        };
    }

    /// Tests that the converter built from the given input correctly converts.
    macro_rules! test_converter {
        ($name:ident, $input:literal, $(#$macros:tt)+) => {
            $(
                #$macros
            )+
            fn $name(
                #[case] expected: Option<&str>,
                #[case] symbol_source: &str,
                #[case] symbol_destination: &str,
                #[case] magnitude_source: &str,
            ) {
                lazy_static! {
                    static ref CONVERTER: Result<Converter, Error> = {
                        // Write the test input to a temporary file.
                        let (mut file_temp, path_temp)
                        = NamedTempFile::new().unwrap().into_parts();

                        file_temp.write_all($input.as_bytes()).unwrap();
                        
                        // Make sure data is written.
                        drop(file_temp);

                        Converter::build(vec![path_temp])
                    };
                }

                // Ensure the converter exists.
                let converter = &*CONVERTER;

                // Empty inputs indicate a "build test."
                if symbol_source.is_empty() && symbol_destination.is_empty()
                && magnitude_source.is_empty() {
                    match (expected, converter) {
                        (None, Err(_)) => {
                            // Pass.
                        },
                        (None, Ok(_)) => {
                            panic!("Expected failed build");
                        },
                        (Some(_), Err(error)) => {
                            panic!("Build failed: {:?}", error);
                        },
                        (Some(_), Ok(_)) => {
                            // Pass.
                        }
                    }
                }
                // Perform a "conversion test."
                else {
                    let converter = (&*CONVERTER).as_ref().unwrap();

                    assert_converter!(
                        converter,
                        expected,
                        symbol_source,
                        symbol_destination,
                        magnitude_source
                    );
                }

            }
        };
    }

    test_converter!(test_build_1,
        "B | AAA",
        #[rstest]
        #[case(Some("") , "" , "" , "")]
        #[trace]
    );
    test_converter!(test_build_2,
        "B | AAA
        B | AAB",
        #[rstest]
        #[case(Some("") , "" , "" , "")]
        #[trace]
    );
    test_converter!(test_build_3,
        "B | AAA
        B | AAA",
        #[rstest]
        #[case(None , "" , "" , "")]
        #[trace]
    );
    test_converter!(test_named_1,
        "B | AAA
        U | a | AAA | 1",
        #[rstest]
        #[case(Some("1") , "a"         , "a" , "1")]
        #[case(Some("1") , "\u{00AA}"  , "a" , "1")]
        #[case(Some("1") , "\u{1D43}"  , "a" , "1")]
        #[case(Some("1") , "\u{2090}"  , "a" , "1")]
        #[case(Some("1") , "\u{24D0}"  , "a" , "1")]
        #[case(Some("1") , "\u{FF41}"  , "a" , "1")]
        #[case(Some("1") , "\u{1D41A}" , "a" , "1")]
        #[case(Some("1") , "\u{1D44E}" , "a" , "1")]
        #[case(Some("1") , "\u{1D482}" , "a" , "1")]
        #[case(Some("1") , "\u{1D4B6}" , "a" , "1")]
        #[case(Some("1") , "\u{1D4EA}" , "a" , "1")]
        #[case(Some("1") , "\u{1D51E}" , "a" , "1")]
        #[case(Some("1") , "\u{1D552}" , "a" , "1")]
        #[case(Some("1") , "\u{1D586}" , "a" , "1")]
        #[case(Some("1") , "\u{1D5BA}" , "a" , "1")]
        #[case(Some("1") , "\u{1D5EE}" , "a" , "1")]
        #[case(Some("1") , "\u{1D622}" , "a" , "1")]
        #[case(Some("1") , "\u{1D656}" , "a" , "1")]
        #[case(Some("1") , "\u{1D68A}" , "a" , "1")]
        #[trace]
    );
    test_converter!(test_named_2,
        "U | a | AAA | 1",
        #[rstest]
        #[case(None , "" , "" , "")]
        #[trace]
    );
    test_converter!(test_named_3,
        "B | AAA
        U | a | AAA | 1
        U | b | AAA | 100",
        #[rstest]
        #[case(Some("7/5")     , "a" , "a" , "7/5")]
        #[case(Some("7/500")   , "a" , "b" , "7/5")]
        #[case(Some("140")     , "b" , "a" , "7/5")]
        #[case(Some("7/5")     , "b" , "b" , "7/5")]
        #[case(Some("700/5")   , "a" , "a" , "700/5")]
        #[case(Some("7/5")     , "a" , "b" , "700/5")]
        #[case(Some("14000")   , "b" , "a" , "700/5")]
        #[case(Some("700/5")   , "b" , "b" , "700/5")]
        #[case(Some("7/500")   , "a" , "a" , "7/500")]
        #[case(Some("7/50000") , "a" , "b" , "7/500")]
        #[case(Some("7/5")     , "b" , "a" , "7/500")]
        #[case(Some("7/500")   , "b" , "b" , "7/500")]
        #[trace]
    );
    test_converter!(test_named_4,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | b | BBB | 100",
        #[rstest]
        #[case(Some("7/5") , "a" , "a" , "7/5")]
        #[case(None        , "a" , "b" , "7/5")]
        #[case(None        , "b" , "a" , "7/5")]
        #[case(Some("7/5") , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_5,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | a | BBB | 1",
        #[rstest]
        #[case(Some("7/5") , "a" , "a" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_6,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | a | BBB | 1
        U | b | AAA | 1
        U | b | BBB | 1",
        #[rstest]
        #[case(Some("7/5") , "a" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_7,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | a | BBB | 1
        U | b | AAA | 1
        U | b | BBB | 100",
        #[rstest]
        #[case(None , "a" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_8,
        "B | AAA
        U | a | AAA | 3/2
        U | b | AAA | 1/4",
        #[rstest]
        #[case(Some("30")   , "a" , "b" , "5")]
        #[case(Some("78/7") , "a" , "b" , "13/7")]
        #[trace]
    );
    test_converter!(test_named_9,
        "B | TMP
        U | K | TMP | 1
        U | C | TMP | 1+273.15",
        #[rstest]
        #[case(Some("273.15") , "C" , "K" , "0")]
        #[case(Some("0")      , "C" , "K" , "-273.15")]
        #[case(Some("373.15") , "C" , "K" , "100")]
        #[trace]
    );
    test_converter!(test_named_10,
        "B | TMP
        U | K | TMP | 1+-273.15
        U | C | TMP | 1",
        #[rstest]
        #[case(Some("273.15") , "C" , "K" , "0")]
        #[case(Some("0")      , "C" , "K" , "-273.15")]
        #[case(Some("373.15") , "C" , "K" , "100")]
        #[trace]
    );
    test_converter!(test_named_11,
        "B | TMP
        U | K | TMP | 1
        U | F | TMP | 5/9+45967/180",
        #[rstest]
        #[case(Some("45967/180") , "F" , "K" , "0")] // 255.37(2)
        #[case(Some("46967/180") , "F" , "K" , "10")] // 260.92(7)
        #[trace]
    );
    test_converter!(test_named_12,
        "B | ANG
        U | rad | ANG | 1
        U | deg | ANG | pi/180",
        #[rstest]
        #[case(Some("3")      , "rad" , "rad" , "3")]
        #[case(Some("540/pi") , "rad" , "deg" , "3")]
        #[case(Some("pi/60")  , "deg" , "rad" , "3")]
        #[case(Some("3")      , "deg" , "deg" , "3")]
        #[trace]
    );
    test_converter!(test_named_13,
        "B | AAA
        B | BBB
        U | a | AAA*BBB | 1",
        #[rstest]
        #[case(Some("1") , "a" , "a" , "1")]
        #[trace]
    );
    test_converter!(test_named_14,
        "B | AAA
        U | a | AAA*BBB | 1",
        #[rstest]
        #[case(None , "" , "" , "")]
        #[trace]
    );
    test_converter!(test_named_15,
        "B | AAA
        B | BBB
        U | a | AAA*BBB | 1
        U | b | AAA*BBB | 100",
        #[rstest]
        #[case(Some("7/5")   , "a" , "a" , "7/5")]
        #[case(Some("7/500") , "a" , "b" , "7/5")]
        #[case(Some("140")   , "b" , "a" , "7/5")]
        #[case(Some("7/5")   , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_16,
        "B | AAA
        B | BBB
        U | a | AAA^2*BBB^-2 | 1
        U | b | AAA^2*BBB^-2 | 100",
        #[rstest]
        #[case(Some("7/5")   , "a" , "a" , "7/5")]
        #[case(Some("7/500") , "a" , "b" , "7/5")]
        #[case(Some("140")   , "b" , "a" , "7/5")]
        #[case(Some("7/5")   , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_17,
        "B | AAA
        B | BBB
        U | a | AAA^2*BBB^-2 | 1
        U | b | AAA^2*BBB^-1 | 100",
        #[rstest]
        #[case(Some("7/5") , "a" , "a" , "7/5")]
        #[case(None        , "a" , "b" , "7/5")]
        #[case(None        , "b" , "a" , "7/5")]
        #[case(Some("7/5") , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_18,
        "B | AAA
        U | a | AAA | 1
        U | b | AAA^-1 | 1",
        #[rstest]
        #[case(Some("7/5") , "a" , "a" , "7/5")]
        #[case(Some("5/7") , "a" , "b" , "7/5")]
        #[case(Some("5/7") , "b" , "a" , "7/5")]
        #[case(Some("7/5") , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_19,
        "B | AAA
        U | a | AAA | 1
        U | b | AAA | 1
        U | b | AAA^-1 | 1",
        #[rstest]
        #[case(Some("7/5") , "a" , "a" , "7/5")]
        #[case(None        , "a" , "b" , "7/5")]
        #[case(None        , "b" , "a" , "7/5")]
        #[case(None        , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_20,
        "B | AAA
        B | BBB
        U | a | AAA^2*BBB^-2 | 1
        U | b | BBB^-2*AAA^2 | 100",
        #[rstest]
        #[case(Some("7/5")   , "a" , "a" , "7/5")]
        #[case(Some("7/500") , "a" , "b" , "7/5")]
        #[case(Some("140")   , "b" , "a" , "7/5")]
        #[case(Some("7/5")   , "b" , "b" , "7/5")]
        #[trace]
    );
    test_converter!(test_named_21,
        "B | AAA
        B | BBB
        P | a | 100
        U | b | AAA | 1
        U | ab | BBB | 1
        U | za | AAA | 5
        U | zb | BBB | 6",
        #[rstest]
        #[case(Some("20")  , "ab" , "za" , "1")]
        #[case(Some("1/6") , "ab" , "zb" , "1")]
        #[case(Some("1")   , "ab" , "ab" , "1")]
        #[trace]
    );
    test_converter!(test_prefixed_1,
        "B | AAA
        P | G | 42
        U | Hz | AAA | 1",
        #[rstest]
        #[case(Some("1") , "Hz"       , "Hz"  , "1")]
        #[case(Some("1") , "GHz"      , "GHz" , "1")]
        #[case(Some("1") , "\u{3393}" , "GHz" , "1")]
        #[trace]
    );
    test_converter!(test_prefixed_2,
        "B | AAA
        P | a | 1",
        #[rstest]
        #[case(Some("") , "" , "" , "")]
        #[trace]
    );
    test_converter!(test_prefixed_3,
        "B | AAA
        P | m | 1/1000
        P | k | 1000
        U | a | AAA | 1",
        #[rstest]
        #[case(Some("1")         , "a"  , "a"  , "1")]
        #[case(Some("1000")      , "a"  , "ma" , "1")]
        #[case(Some("1/1000")    , "a"  , "ka" , "1")]
        #[case(Some("1/1000")    , "ma" , "a"  , "1")]
        #[case(Some("1")         , "ma" , "ma" , "1")]
        #[case(Some("1/1000000") , "ma" , "ka" , "1")]
        #[case(Some("1000")      , "ka" , "a"  , "1")]
        #[case(Some("1000000")   , "ka" , "ma" , "1")]
        #[case(Some("1")         , "ka" , "ka" , "1")]
        #[trace]
    );
    test_converter!(test_prefixed_4,
        "B | TMP
        U | K | TMP | 1
        U | C | TMP | 1+273.15
        P | m | 1/1000",
        #[rstest]
        #[case(Some("1")        , "K"  , "K"  , "1")]
        #[case(Some("1000")     , "K"  , "mK" , "1")]
        #[case(Some("-272.15")   , "K"  , "C"  , "1")]
        #[case(Some("-272150")  , "K"  , "mC" , "1")]
        #[case(Some("1/1000")   , "mK" , "K"  , "1")]
        #[case(Some("1")        , "mK" , "mK" , "1")]
        #[case(Some("-273.149") , "mK" , "C"  , "1")]
        #[case(Some("-273149")  , "mK" , "mC" , "1")]
        #[case(Some("274.15")   , "C"  , "K"  , "1")]
        #[case(Some("274150")   , "C"  , "mK" , "1")]
        #[case(Some("1")        , "C"  , "C"  , "1")]
        #[case(Some("1000")     , "C"  , "mC" , "1")]
        #[case(Some("273.151")  , "mC" , "K"  , "1")]
        #[case(Some("273151")   , "mC" , "mK" , "1")]
        #[case(Some("1/1000")   , "mC" , "C"  , "1")]
        #[case(Some("1")        , "mC" , "mC" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_1,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | b | BBB | 1",
        #[rstest]
        #[case(Some("1") , "a\u{22C5}b"   , "a*b" , "1")]
        #[case(Some("1") , "a \u{22C5} b" , "a*b" , "1")]
        #[case(Some("1") , "a\u{00B7}b"   , "a*b" , "1")]
        #[case(Some("1") , "a \u{00B7} b" , "a*b" , "1")]
        #[case(Some("1") , "a*b"          , "a*b" , "1")]
        #[case(Some("1") , "a * b"        , "a*b" , "1")]
        // #[case(Some("1") , "a-b"          , "a*b" , "1")]
        // #[case(Some("1") , "a - b"        , "a*b" , "1")]
        // #[case(Some("1") , "a b"          , "a*b" , "1")]
        // #[case(Some("1") , "a   b"        , "a*b" , "1")]
        // #[case(Some("1") , "a\u{00A0}b"   , "a*b" , "1")]
        // #[case(Some("1") , "a \u{2009} b" , "a*b" , "1")]
        #[case(Some("1") , "b\u{22C5}a"   , "a*b" , "1")]
        #[case(Some("1") , "b \u{22C5} a" , "a*b" , "1")]
        #[case(Some("1") , "b\u{00B7}a"   , "a*b" , "1")]
        #[case(Some("1") , "b \u{00B7} a" , "a*b" , "1")]
        #[case(Some("1") , "b*a"          , "a*b" , "1")]
        #[case(Some("1") , "b * a"        , "a*b" , "1")]
        // #[case(Some("1") , "b-a"          , "a*b" , "1")]
        // #[case(Some("1") , "b - a"        , "a*b" , "1")]
        // #[case(Some("1") , "b a"          , "a*b" , "1")]
        // #[case(Some("1") , "b   a"        , "a*b" , "1")]
        // #[case(Some("1") , "b\u{00A0}a"   , "a*b" , "1")]
        // #[case(Some("1") , "b \u{2009} a" , "a*b" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_2,
        "B | AAA
        B | BBA
        B | BBB
        U | abcd | AAA | 1
        U | ab | BBA | 1
        U | cd | BBB | 1
        U | za | AAA | 5
        U | zb | BBA*BBB | 6",
        #[rstest]
        #[case(Some("1/5") , "abcd" , "za" , "1")]
        // zb -> 1/6
        // zc -> 1/7
        #[trace]
    );
    test_converter!(test_unnamed_3,
        "B | AAA
        B | BBA
        B | BBB
        B | CCA
        B | CCB
        B | CCC
        B | CCD
        U | abcd | AAA | 1
        U | ab | BBA | 1
        U | cd | BBB | 1
        U | a | CCA | 1
        U | b | CCB | 1
        U | c | CCC | 1
        U | d | CCD | 1
        U | za | AAA | 5
        U | zb | BBA*BBB | 6
        U | zc | CCA*CCB*CCC*CCD | 7",
        #[rstest]
        #[case(Some("1/5") , "abcd" , "za" , "1")]
        // zb -> 1/6
        // zc -> 1/7
        #[trace]
    );
    test_converter!(test_unnamed_4,
        "B | AAA
        B | BBA
        B | BBB
        B | CCA
        B | CCB
        B | CCC
        B | CCD
        U | abcd | AAA | 1
        U | ab | BBA | 1
        U | cd | BBB | 1
        U | a | CCA | 1
        U | b | CCB | 1
        U | d | CCD | 1
        U | za | AAA | 5
        U | zb | BBA*BBB | 6
        U | zc | CCA*CCB*CCC*CCD | 7",
        #[rstest]
        #[case(Some("1/5") , "abcd" , "za" , "1")]
        // zb -> 1/6
        #[case(None        , "abcd" , "zc" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_5,
        "B | AAA
        U | a | AAA | 1
        U | b | AAA | 1
        U | ab | AAA^2 | 1
        U | z | AAA^2 | 5",
        #[rstest]
        #[case(Some("1/5") , "ab"  , "z" , "1")]
        #[case(Some("1/5") , "a^2" , "z" , "1")]
        #[case(Some("1/5") , "b^2" , "z" , "1")]
        // #[case(Some("1/5") , "a2"  , "z" , "1")]
        // #[case(Some("1/5") , "b2"  , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_6,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | b | BBB | 1
        U | z | AAA*BBB^-1 | 5",
        #[rstest]
        #[case(Some("1/5") , "a/b"          , "z" , "1")]
        #[case(Some("1/5") , "a /b"         , "z" , "1")]
        #[case(Some("1/5") , "a/ b"         , "z" , "1")]
        #[case(Some("1/5") , "a / b"        , "z" , "1")]
        #[case(Some("1/5") , "a\u{2044}b"   , "z" , "1")]
        #[case(Some("1/5") , "a \u{2044}b"  , "z" , "1")]
        #[case(Some("1/5") , "a\u{2044} b"  , "z" , "1")]
        #[case(Some("1/5") , "a \u{2044} b" , "z" , "1")]
        #[case(Some("1/5") , "a\u{2215}b"   , "z" , "1")]
        #[case(Some("1/5") , "a \u{2215}b"  , "z" , "1")]
        #[case(Some("1/5") , "a\u{2215} b"  , "z" , "1")]
        #[case(Some("1/5") , "a \u{2215} b" , "z" , "1")]
        #[case(Some("1/5") , "a*b^-1"       , "z" , "1")]
        // #[case(Some("1/5") , "a*b-1"        , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_7,
        "B | AAA
        B | BBB
        U | a | AAA | 1
        U | b | BBB | 1
        U | z | AAA*BBB^-1 | 5",
        #[rstest]
        #[case(Some("1/50") , "a/10b"           , "z" , "1")]
        #[case(Some("1/50") , "a /10b"          , "z" , "1")]
        #[case(Some("1/50") , "a/ 10b"          , "z" , "1")]
        #[case(Some("1/50") , "a / 10b"         , "z" , "1")]
        #[case(Some("1/50") , "a\u{2044}10b"    , "z" , "1")]
        #[case(Some("1/50") , "a \u{2044}10b"   , "z" , "1")]
        #[case(Some("1/50") , "a\u{2044} 10b"   , "z" , "1")]
        #[case(Some("1/50") , "a \u{2044} 10b"  , "z" , "1")]
        #[case(Some("1/50") , "a\u{2215}10b"    , "z" , "1")]
        #[case(Some("1/50") , "a \u{2215}10b"   , "z" , "1")]
        #[case(Some("1/50") , "a\u{2215} 10b"   , "z" , "1")]
        #[case(Some("1/50") , "a \u{2215} 10b"  , "z" , "1")]
        #[case(Some("1/50") , "a/10 b"          , "z" , "1")]
        #[case(Some("1/50") , "a /10 b"         , "z" , "1")]
        #[case(Some("1/50") , "a/ 10 b"         , "z" , "1")]
        #[case(Some("1/50") , "a / 10 b"        , "z" , "1")]
        #[case(Some("1/50") , "a\u{2044}10 b"   , "z" , "1")]
        #[case(Some("1/50") , "a \u{2044}10 b"  , "z" , "1")]
        #[case(Some("1/50") , "a\u{2044} 10 b"  , "z" , "1")]
        #[case(Some("1/50") , "a \u{2044} 10 b" , "z" , "1")]
        #[case(Some("1/50") , "a\u{2215}10 b"   , "z" , "1")]
        #[case(Some("1/50") , "a \u{2215}10 b"  , "z" , "1")]
        #[case(Some("1/50") , "a\u{2215} 10 b"  , "z" , "1")]
        #[case(Some("1/50") , "a \u{2215} 10 b" , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_8,
        "B | AAA
        B | BBB
        U | a | AAA | 5
        U | b | BBB | 2
        U | z | AAA^2*BBB | 5",
        #[rstest]
        #[case(Some("10") , "a^2\u{22C5}b"   , "z" , "1")]
        #[case(Some("10") , "a^2 \u{22C5} b" , "z" , "1")]
        #[case(Some("10") , "a^2\u{00B7}b"   , "z" , "1")]
        #[case(Some("10") , "a^2 \u{00B7} b" , "z" , "1")]
        #[case(Some("10") , "a^2*b"          , "z" , "1")]
        #[case(Some("10") , "a^2 * b"        , "z" , "1")]
        #[case(Some("10") , "b\u{22C5}a^2"   , "z" , "1")]
        #[case(Some("10") , "b \u{22C5} a^2" , "z" , "1")]
        #[case(Some("10") , "b\u{00B7}a^2"   , "z" , "1")]
        #[case(Some("10") , "b \u{00B7} a^2" , "z" , "1")]
        #[case(Some("10") , "b*a^2"          , "z" , "1")]
        #[case(Some("10") , "b * a^2"        , "z" , "1")]
        // #[case(Some("10") , "a2\u{22C5}b"    , "z" , "1")]
        // #[case(Some("10") , "a2 \u{22C5} b"  , "z" , "1")]
        // #[case(Some("10") , "a2\u{00B7}b"    , "z" , "1")]
        // #[case(Some("10") , "a2 \u{00B7} b"  , "z" , "1")]
        // #[case(Some("10") , "a2*b"           , "z" , "1")]
        // #[case(Some("10") , "a2 * b"         , "z" , "1")]
        // #[case(Some("10") , "b\u{22C5}a2"    , "z" , "1")]
        // #[case(Some("10") , "b \u{22C5} a2"  , "z" , "1")]
        // #[case(Some("10") , "b\u{00B7}a2"    , "z" , "1")]
        // #[case(Some("10") , "b \u{00B7} a2"  , "z" , "1")]
        // #[case(Some("10") , "b*a2"           , "z" , "1")]
        // #[case(Some("10") , "b * a2"         , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_9,
        "B | AAA
        P | k | 1000
        U | m | AAA | 1",
        #[rstest]
        #[case(Some("1")            , "m^2"  , "m^2"  , "1")]
        #[case(Some("1/1000000")    , "m^2"  , "km^2" , "1")]
        #[case(Some("1000000")      , "km^2" , "m^2"  , "1")]
        #[case(Some("1")            , "km^2" , "km^2" , "1")]
        #[case(Some("1")            , "m^3"  , "m^3"  , "1")]
        #[case(Some("1/1000000000") , "m^3"  , "km^3" , "1")]
        #[case(Some("1000000000")   , "km^3" , "m^3"  , "1")]
        #[case(Some("1")            , "km^3" , "km^3" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_10,
        "B | AAA
        B | BBB
        U | a | AAA | 5
        U | b | BBB | 2
        U | z | AAA^-1*BBB | 5",
        #[rstest]
        #[case(Some("2/25") , "a^-1\u{22C5}b"   , "z" , "1")]
        #[case(Some("2/25") , "a^-1 \u{22C5} b" , "z" , "1")]
        #[case(Some("2/25") , "a^-1\u{00B7}b"   , "z" , "1")]
        #[case(Some("2/25") , "a^-1 \u{00B7} b" , "z" , "1")]
        #[case(Some("2/25") , "a^-1*b"          , "z" , "1")]
        #[case(Some("2/25") , "a^-1 * b"        , "z" , "1")]
        #[case(Some("2/25") , "b\u{22C5}a^-1"   , "z" , "1")]
        #[case(Some("2/25") , "b \u{22C5} a^-1" , "z" , "1")]
        #[case(Some("2/25") , "b\u{00B7}a^-1"   , "z" , "1")]
        #[case(Some("2/25") , "b \u{00B7} a^-1" , "z" , "1")]
        #[case(Some("2/25") , "b*a^-1"          , "z" , "1")]
        #[case(Some("2/25") , "b * a^-1"        , "z" , "1")]
        // #[case(Some("2/25") , "a-1\u{22C5}b"    , "z" , "1")]
        // #[case(Some("2/25") , "a-1 \u{22C5} b"  , "z" , "1")]
        // #[case(Some("2/25") , "a-1\u{00B7}b"    , "z" , "1")]
        // #[case(Some("2/25") , "a-1 \u{00B7} b"  , "z" , "1")]
        // #[case(Some("2/25") , "a-1*b"           , "z" , "1")]
        // #[case(Some("2/25") , "a-1 * b"         , "z" , "1")]
        // #[case(Some("2/25") , "b\u{22C5}a-1"    , "z" , "1")]
        // #[case(Some("2/25") , "b \u{22C5} a-1"  , "z" , "1")]
        // #[case(Some("2/25") , "b\u{00B7}a-1"    , "z" , "1")]
        // #[case(Some("2/25") , "b \u{00B7} a-1"  , "z" , "1")]
        // #[case(Some("2/25") , "b*a-1"           , "z" , "1")]
        // #[case(Some("2/25") , "b * a-1"         , "z" , "1")]
        #[case(Some("2/25") , "b/a"             , "z" , "1")]
        #[case(Some("2/25") , "b\u{2044}a"      , "z" , "1")]
        #[case(Some("2/25") , "b\u{2215}a"      , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_11,
        "B | AAA
        B | BBB
        U | a | AAA | 5
        U | b | BBB | 2
        U | z | AAA^-2*BBB | 5",
        #[rstest]
        #[case(Some("2/125") , "a^-2\u{22C5}b"   , "z" , "1")]
        #[case(Some("2/125") , "a^-2 \u{22C5} b" , "z" , "1")]
        #[case(Some("2/125") , "a^-2\u{00B7}b"   , "z" , "1")]
        #[case(Some("2/125") , "a^-2 \u{00B7} b" , "z" , "1")]
        #[case(Some("2/125") , "a^-2*b"          , "z" , "1")]
        #[case(Some("2/125") , "a^-2 * b"        , "z" , "1")]
        #[case(Some("2/125") , "b\u{22C5}a^-2"   , "z" , "1")]
        #[case(Some("2/125") , "b \u{22C5} a^-2" , "z" , "1")]
        #[case(Some("2/125") , "b\u{00B7}a^-2"   , "z" , "1")]
        #[case(Some("2/125") , "b \u{00B7} a^-2" , "z" , "1")]
        #[case(Some("2/125") , "b*a^-2"          , "z" , "1")]
        #[case(Some("2/125") , "b * a^-2"        , "z" , "1")]
        // #[case(Some("2/125") , "a-2\u{22C5}b"    , "z" , "1")]
        // #[case(Some("2/125") , "a-2 \u{22C5} b"  , "z" , "1")]
        // #[case(Some("2/125") , "a-2\u{00B7}b"    , "z" , "1")]
        // #[case(Some("2/125") , "a-2 \u{00B7} b"  , "z" , "1")]
        // #[case(Some("2/125") , "a-2*b"           , "z" , "1")]
        // #[case(Some("2/125") , "a-2 * b"         , "z" , "1")]
        // #[case(Some("2/125") , "b\u{22C5}a-2"    , "z" , "1")]
        // #[case(Some("2/125") , "b \u{22C5} a-2"  , "z" , "1")]
        // #[case(Some("2/125") , "b\u{00B7}a-2"    , "z" , "1")]
        // #[case(Some("2/125") , "b \u{00B7} a-2"  , "z" , "1")]
        // #[case(Some("2/125") , "b*a-2"           , "z" , "1")]
        // #[case(Some("2/125") , "b * a-2"         , "z" , "1")]
        // #[case(Some("2/125") , "b/a^2"           , "z" , "1")]
        // #[case(Some("2/125") , "b\u{2044}a^2"    , "z" , "1")]
        // #[case(Some("2/125") , "b\u{2215}a^2"    , "z" , "1")]
        // #[case(Some("2/125") , "b/a2"            , "z" , "1")]
        // #[case(Some("2/125") , "b\u{2044}a2"     , "z" , "1")]
        // #[case(Some("2/125") , "b\u{2215}a2"     , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_12,
        "B | AAA
        B | BBB
        U | m | AAA | 1
        U | s | BBB | 1",
        #[rstest]
        #[case(Some("1") , "m/s"      , "m/s" , "1")]
        #[case(Some("1") , "\u{33A7}" , "m/s" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_13,
        "B | AAA
        B | BBB
        B | CCC
        U | a | AAA | 5
        U | b | BBB | 2
        U | c | CCC | 3
        U | z | AAA^-2*BBB*CCC | 5",
        #[rstest]
        #[case(Some("6/125") , "a^-2*b*c" , "z" , "1")]
        #[case(Some("6/125") , "a^-2*c*b" , "z" , "1")]
        #[case(Some("6/125") , "b*a^-2*c" , "z" , "1")]
        #[case(Some("6/125") , "b*c*a^-2" , "z" , "1")]
        #[case(Some("6/125") , "c*a^-2*b" , "z" , "1")]
        #[case(Some("6/125") , "c*b*a^-2" , "z" , "1")]
        #[case(Some("6/125") , "b*c/a^2"  , "z" , "1")]
        #[case(Some("6/125") , "c*b/a^2"  , "z" , "1")]
        #[trace]
    );
    test_converter!(test_unnamed_14,
        "B | AAA
        B | BBB
        B | CCC
        U | a | AAA | 5
        U | b | BBB | 2
        U | c | CCC | 3
        U | z | AAA^-2*BBB*CCC^-1 | 5",
        #[rstest]
        #[case(Some("2/375") , "a^-2*b*c^-1" , "z" , "1")]
        #[case(Some("2/375") , "a^-2*c^-1*b" , "z" , "1")]
        #[case(Some("2/375") , "b*a^-2*c^-1" , "z" , "1")]
        #[case(Some("2/375") , "b*c^-1*a^-2" , "z" , "1")]
        #[case(Some("2/375") , "c^-1*a^-2*b" , "z" , "1")]
        #[case(Some("2/375") , "c^-1*b*a^-2" , "z" , "1")]
        #[case(Some("2/375") , "b/a^2*c^1"   , "z" , "1")]
        #[case(Some("2/375") , "b/c^1*a^2"   , "z" , "1")]
        #[trace]
    );

    /// Tests the actual production converter.
    #[rstest]
    #[case(Some("1") , "s"   , "min" , "60")]
    #[case(Some("1") , "min" , "h"   , "60")]
    #[case(Some("1") , "h"   , "d"   , "24")]

    #[case(Some("1000")    , "km" , "m"  , "1")]
    #[case(Some("1000")    , "km" , "m"  , "1")]
    #[case(Some("25.4")    , "in" , "mm" , "1")]
    #[case(Some("-273.15") , "K"  , "°C" , "0")]
    #[trace]
    fn test_converter_production(
        #[case] expected: Option<&str>,
        #[case] symbol_source: &str,
        #[case] symbol_destination: &str,
        #[case] magnitude_source: &str,
    ) {
        lazy_static! {
            static ref CONVERTER: Converter = Converter::new();
        }

        assert_converter!(
            &*CONVERTER,
            expected,
            symbol_source,
            symbol_destination,
            magnitude_source
        );
    }

    /// Tests for the existence of certain units in the actual production
    /// converter and that certain combinations are convertible with each other.
    #[rstest]
    #[case::duration(vec![
        "s",
        "sec",

        // Being the first case in this series of tests, the responsibility for
        // testing all of the prefixes falls to this one. It is too much work to
        // perform this check on *every* unit.
        "ys",
        "zs",
        "as",
        "fs",
        "ps",
        "ns",
        "μs",
        "us",
        "mcs",
        "ms",
        "cs",
        "ds",
        "das",
        "dks",
        "hs",
        "ks",
        "Ms",
        "Gs",
        "Ts",
        "Ps",
        "Es",
        "Zs",
        "Ys",

        "min",
        "h",
        "hr",
        "d",
        "day",
        "wk",
        "a_j",
        "aj",
        "a",
        "sol",
    ])]
    #[case::length(vec![
        "m",

        "NM",
        "Å",
        "A",
        "ly",
        "pc",

        "thou",
        "mil",
        "in",
        "ft",
        "yd",

        "rd",
        "fur",
        "mi",
    ])]
    #[case::mass(vec![
        "kg",

        "eV/c^2",
        "eV",

        "lb",
        "oz",
    ])]
    #[case::current(vec![
        "A",
    ])]
    #[case::temperature(vec![
        "K",
        "°C",

        "°K",

        // "°F",
        // "°Ra",
    ])]
    #[case::amountofsubstance(vec![
        "mol",
    ])]
    #[case::luminosity(vec![
        "cd",
    ])]
    #[case::planeangle(vec![
        "rad",

        // The SI brochure prescribes the existence of the metre per metre (m/m)
        // as a synonym of the radian; this behaviour is *not* implemented by
        // the converter.

        "°",
        "deg",
        "′",
        "'",
        "arcmin",
        "″",
        "′′",
        "\"",
        "''",
        "arcsec",
        "tr"
    ])]
    #[case::solidangle(vec![
        "sr",

        // The SI brochure prescribes the existence of the metre squared per
        // metre squared (m^2/m^2) as a synonym of the steradian; this behaviour
        // is *not* implemented by the converter.
        
        "°^2",
        "deg^2",
        "′^2",
        "'^2",
        "arcmin^2",
        "″^2",
        "′′^2",
        "\"^2",
        "''^2",
        "arcsec^2",
        "sp",
    ])]
    #[case::frequency(vec![
        "Hz",
        "s^-1",

        "min^-1",
        "h^-1",
        "hr^-1",
        "d^-1",
        "day^-1",
        "wk^-1",
        "a_j^-1",
        "aj^-1",
        "a^-1",
        "sol^-1",
        "cps",
        "rpm",
        "RPM",
    ])]
    #[case::force(vec![
        "N",
        "kg*m*s^-2",

        "kg_f",
        "kg_F",
        "kgf",
        "kgF",
        "kg",
        "kp",
        "dyn",

        "lb_f",
        "lbf",
        "lb",
        "oz_f",
        "ozf",
        "oz",
    ])]
    #[case::pressure(vec![
        "Pa",
        "kg*m^-1*s^-2",

        "bar",
        "atm",
        "Torr",
        "mmHg",
        "Ba",

        "lb_f/in^2",
        "oz_f/in^2",
        "psi",
        "ksi",
    ])]
    #[case::energy(vec![
        "J",
        "kg*m^2*s^-2",
        "N*m",

        "kW*h",
        "kWh",
        "erg",
    ])]
    #[case::power(vec![
        "W",
        "kg*m^2*s^-3",
        "J/s",

        "PS",
    ])]

    #[case(vec!["C", "A*s"])]
    #[case(vec!["V", "kg*m^2*s^-3*A^-1", "W/A"])]
    #[case(vec!["F", "kg^-1*m^-2*s^4*A^2", "C/V"])]
    #[case(vec!["Ω", "kg*m^2*s^-3*A^-2", "V/A"])]
    #[case(vec!["S", "kg^-1*m^-2*s^3*A^2", "A/V"])]
    #[case(vec!["Wb", "kg*m^2*s^-2*A^-1", "V*s"])]
    #[case(vec!["T", "kg*s^-2*A^-1", "Wb/m^2"])]
    #[case(vec!["H", "kg*m^2*s^-2*A^-2", "Wb/A"])]
    #[case(vec!["lm", "cd*sr"])]
    #[case(vec!["lx", "cd*sr*m^-2", "lm/m^2"])]
    #[case(vec!["Bq", "s^-1"])]
    #[case(vec!["Gy", "m^2*s^-2", "J/kg"])]
    #[case(vec!["Sv", "m^2*s^-2", "J/kg"])]
    #[case(vec!["kat", "mol*s^-1"])]

    #[case::area(vec![
        "m^2",

        "ha",
    ])]
    #[case::volume(vec![
        "m^3",

        "cc",
    ])]
    #[case::velocity(vec![
        "m*s^-1",

        "c",
        "kn",
        "kt",
    ])]
    #[case::acceleration(vec![
        "m*s^-2",

        "g_0",
        "g0",
        "g",
        "Gal",
    ])]
    #[trace]
    fn test_converter_production_existence(
        #[case] symbols: Vec<&str>,
    ) {
        lazy_static! {
            static ref CONVERTER: Converter = Converter::new();
        }

        for symbol_source in symbols.iter() {
            for symbol_destination in symbols.iter() {
                let result = CONVERTER.convert(
                    symbol_source,
                    symbol_destination,
                    &Number::one_exact()
                );

                if let Err(error) = result {
                    panic!("Failed to convert between {} and {}: {}", symbol_source, symbol_destination, error);
                }
            }
        }
    }
}