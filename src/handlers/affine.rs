use crate::handlers::UnitHandler;
use crate::number::Number;

pub struct AffineHandler {
    factor: Number,
    offset: Number,
}

impl AffineHandler {
    pub fn new(factor: Number, offset: Number) -> AffineHandler {
        AffineHandler {factor, offset}
    }
}

impl UnitHandler for AffineHandler {
    fn transform_forward(&self, magnitude: Number) -> Number {
        magnitude * &self.factor - &self.offset
    }

    fn transform_reverse(&self, magnitude: Number) -> Number {
        magnitude / &self.factor + &self.offset
    }
}