#[cfg(test)]

#[test]
fn fixtures() {
    let type_error_fixtures = std::fs::read_dir("fixtures/type_errors").unwrap();
    let interpreter_fixtures = std::fs::read_dir("fixtures/interpreter").unwrap();

    for entry in type_error_fixtures.chain(interpreter_fixtures) {
        let entry = entry.unwrap();
        let path = entry.path();
        println!("Analyzing {}", path.display());

        let file_contents = std::fs::read_to_string(path).unwrap();
        let (input, expected_output) = file_contents.split_once("\n---\n").unwrap();

        let mut output_writer = vec![];
        tl::run(input.to_string(), &mut output_writer).unwrap();

        let actual_output = String::from_utf8(output_writer).unwrap();

        let expected_output = expected_output.trim_start_matches('\n').trim_end_matches('\n');
        let actual_output = actual_output.trim_start_matches('\n').trim_end_matches('\n');

        if expected_output != actual_output {
            println!("Test case failed. Input:\n\n{}\n", input);
            println!("Expected output:\n\n{}\n\nActual output:\n\n{}",
                     expected_output, actual_output);
            panic!();
        }
    }
}
