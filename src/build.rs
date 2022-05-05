mod converter;
mod handlers;
mod number;

use itertools::Itertools;
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;
use std::path::PathBuf;

use converter::Converter;

const PATH_DATABASE: &str = "src/database";
const FILENAME_DATA_CONVERTER: &str = "converter.obj";

/// Performs tasks necessary for building the converter.
fn main() {
    let mut path_output = PathBuf::from(env::var("OUT_DIR").unwrap());
    path_output.push(FILENAME_DATA_CONVERTER);

    // Track changes in the database directory.
    println!("cargo:rerun-if-changed={}", PATH_DATABASE);

    // Prevent compilation of parsing code in the final binary.
    println!("cargo:rustc-cfg=mainbuild");

    // Specify location of the converter data.
    println!("cargo:rustc-env=PATH_DATA_CONVERTER={}", path_output.display());

    let mut lines = Vec::with_capacity(1_000);

    // Find and open the database files. These are the files in the database
    // directory that have the .dat extension.
    let paths = fs::read_dir(PATH_DATABASE).unwrap()
    .map(|entry| entry.unwrap())
    .map(|entry| entry.path())
    .filter(|path| path.is_file())
    .filter(|path| path.extension() == Some(OsStr::new("dat")))
    .map(|path| path.canonicalize().unwrap()); // TODO make paths prettier

    for path in paths {
        let file = File::open(&path).unwrap();

        for (line, number)
        in BufReader::new(file).lines().map(Result::unwrap).zip(1..) {
            lines.push((line, format!("{}", path.display()), number));
        }
    }

    let input = lines.iter().map(|(line, _, _)| line).join("\n");

    let converter = input.parse::<Converter>().unwrap_or_else(|error| {
        const DELIMITER: char = ':';

        let message_error_upstream = format!("{}", error);

        let (string_number_line, message_error)
        = message_error_upstream.split_once(DELIMITER).unwrap();

        let number_line = string_number_line.parse::<usize>().unwrap();

        let index_line = number_line - 1;

        let (_, path, number_line) = &lines[index_line];

        eprintln!();
        eprintln!("Error parsing database files:");
        eprintln!("{}:{}:{}", path, number_line, message_error);
        eprintln!();
        
        panic!("Error parsing database files");
    });

    let data_converter = bincode::serialize(&converter).unwrap();

    let mut file_output = File::create(&path_output).unwrap();

    file_output.write_all(&data_converter).unwrap();
}