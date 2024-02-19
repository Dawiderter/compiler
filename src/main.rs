use std::io::Write;
use std::{
    fs::{read_to_string, File},
    path::PathBuf,
};

use clap::Parser;
use compiler::build_code;

#[derive(clap::Parser)]
pub struct CompilerArgs {
    input_file: PathBuf,
    output_file: Option<PathBuf>,
}

pub fn main() {
    let args = CompilerArgs::parse();
    let input = read_to_string(args.input_file).unwrap();

    let mach = build_code(&input);
    let Some(mach) = mach else { return; };

    if let Some(output) = args.output_file {
        let mut file = File::create(output).unwrap();
        writeln!(file, "{}", mach).unwrap();
    } else {
        println!("{}", mach);
    }
}
