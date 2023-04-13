fn main() {
    let input_file = std::env::args().nth(1).unwrap();
    let input = std::fs::read_to_string(input_file).unwrap();

    let mut stdout = std::io::stdout();
    tl::run(input.to_string(), &mut stdout).unwrap();
}
