mod converter;
mod handlers;
mod number;

use std::env;
use std::ffi::OsStr;
use std::fs;
use std::fs::File;
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

    // Find and open the database files. These are the files in the database
    // directory that have the .dat extension.
    let files = fs::read_dir(PATH_DATABASE).unwrap()
    .map(|entry| entry.unwrap())
    .map(|entry| entry.path())
    .filter(|path| path.is_file())
    .filter(|path| path.extension() == Some(OsStr::new("dat")))
    .collect::<Vec<PathBuf>>();

    let converter = Converter::build(files).unwrap_or_else(|error| {
        eprintln!();
        eprintln!("Error parsing database files:");
        eprintln!("{}", error);
        eprintln!();
        panic!("Error parsing database files")
    });

    let data_converter = bincode::serialize(&converter).unwrap();

    let mut file_output = File::create(&path_output).unwrap();

    file_output.write_all(&data_converter).unwrap();
}