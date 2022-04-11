mod converter;
mod handlers;
mod number;

use std::env;

use converter::Converter;
use number::Number;

const DATA_CONVERTER: &[u8] = include_bytes!(env!("PATH_DATA_CONVERTER"));

fn main() {
    let converter = bincode::deserialize::<Converter>(DATA_CONVERTER).unwrap();

    // TODO advanced parsing

    let arguments = env::args().collect::<Vec<String>>();

    let magnitude = arguments[1].parse::<Number>().unwrap();
    let symbol_source = &arguments[2];
    let symbol_destination = &arguments[4];

    match converter.convert(symbol_source, symbol_destination, &magnitude) {
        Ok(result) => {
            println!("{} {}", result, symbol_destination);
        }
        Err(error) => {
            println!("Error: {}", error);
        }
    }
}