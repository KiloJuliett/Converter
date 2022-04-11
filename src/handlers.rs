mod affine;
mod arithmetic;

use anyhow::Error;
use maplit::hashmap;
use lazy_static::lazy_static;
use std::collections::HashMap;

use crate::handlers::affine::AffineHandler;
use crate::number::Number;



/// Builds a table of relation handlers.
macro_rules! handlers_relations {
    ($($name:literal => $handler:expr,)+) => {
        hashmap! [
            $(
                $name => Box::new($handler) as Box<dyn RelationHandler>,
            )*
        ]
    }
}

/// Builds a table of unit handlers.
macro_rules! handlers_units {
    ($($name:literal => $handler:expr,)+) => {
        hashmap! [
            $(
                $name => Box::new($handler) as Box<dyn UnitHandler>,
            )*
        ]
    }
}

/// Parses the string as a magnitude, panicking if not possible.
// TODO I would prefer a method that allows use of const fn, but it's unlikely
// such a method would be as easily maintainable as parsing strings.
macro_rules! number {
    ($string:literal) => {
        $string.parse::<Number>().unwrap()
    };
}

lazy_static! {

    pub static ref HANDLERS_RELATIONS: HashMap<&'static str, Box<dyn RelationHandler>>
    = handlers_relations![
        "factor_2pi" => arithmetic::FactorHandler {factor: number!("2pi")},
        "factor_1div2pi" => arithmetic::FactorHandler {factor: number!("1/2pi")},
        "reciprocal" => arithmetic::ReciprocalHandler {},
    ];
    

    /// The unit handlers in this unit converter.
    pub static ref HANDLERS_UNITS: HashMap<&'static str, Box<dyn UnitHandler>>
    = handlers_units![
        "celsius" => AffineHandler::new(number!("1"), number!("273.15")),
    ];
    
    
    
}





/// Implements the ability to handle quantity relations.
pub trait RelationHandler : Sync {
    /// Transform references.
    fn transform(&self, magnitude: Number) -> Result<Number, Error>;
}

// TODO allow errors
/// Implements the ability to handle unit transformations.
pub trait UnitHandler : Sync {
    /// Transform from reference.
    fn transform_forward(&self, magnitude: Number) -> Number;

    /// Transform to reference.
    fn transform_reverse(&self, magnitude: Number) -> Number;
}



pub trait DesignationHandler : Sync {
    fn convert_forward(&self, magnitude: Number) -> String;
    fn convert_reverse(&self, string: String) -> Number;
}