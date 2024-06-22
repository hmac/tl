use std::path::PathBuf;

use tracing_subscriber;

const USAGE: &'static str = "
Usage:
  tl run <PATH> <FUNC>
  tl test <PATH>
  tl compile <PATH>

  Example:

    tl run foo/bar.tl my_func
    tl test foo/bar.tl
    tl compile foo/bar.tl

";

fn main() {
    tracing_subscriber::fmt::init();

    let mut args = std::env::args();
    args.next(); // skip program name

    match args.next() {
        Some(cmd) => match cmd.as_str() {
            "run" => {
                let input_file = args.next().expect(USAGE);
                let function = args.next().expect(USAGE);
                let stdout = std::io::stdout();

                let mut runner = tl::Runner::from_path(&PathBuf::from(input_file), stdout).unwrap();

                let result = runner.run(&function).unwrap();
                println!("{}", result);
            }
            "test" => {
                let input_file = args.next().expect(USAGE);
                let stdout = std::io::stdout();

                let mut runner = tl::Runner::from_path(&PathBuf::from(input_file), stdout).unwrap();

                runner.run_tests().unwrap();
            }
            "compile" => {
                let input_file = args.next().expect(USAGE);
                let stdout = std::io::stdout();

                let runner = tl::Runner::from_path(&PathBuf::from(input_file), stdout).unwrap();
                let compiler = runner.compile().unwrap();
                println!("{}", compiler.program);
            }
            _ => fail(),
        },
        None => fail(),
    }
}

fn fail() {
    println!("{}", USAGE);
    std::process::exit(-1)
}
