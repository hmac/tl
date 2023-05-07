use std::path::PathBuf;

const USAGE: &'static str = "
Usage:
  tl <PATH> <FUNC>

  Example:

    tl foo/bar.tl my_func
";

fn main() {
    let input_file = std::env::args().nth(1).expect(USAGE);
    let function = std::env::args().nth(2).expect(USAGE);
    let stdout = std::io::stdout();

    let mut runner = tl::Runner::from_path(&PathBuf::from(input_file), stdout).unwrap();

    let result = runner.run(&function).unwrap();
    println!("{}", result);
}
