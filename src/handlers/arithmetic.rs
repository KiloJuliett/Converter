use anyhow::ensure;
use anyhow::Error;

use crate::handlers::RelationHandler;
use crate::number::Number;

pub struct FactorHandler {
    pub factor: Number,
}

impl RelationHandler for FactorHandler {
    fn transform(&self, magnitude: Number) -> Result<Number, Error> {
        Ok(&self.factor * magnitude)
    }
}

pub struct ReciprocalHandler;

impl RelationHandler for ReciprocalHandler {
    fn transform(&self, magnitude: Number) -> Result<Number, Error> {
        ensure!(magnitude != Number::zero_exact(), "Division by zero!"); // TODO better string

        Ok(magnitude.recip())
    }
}