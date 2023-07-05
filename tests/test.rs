#[cfg(test)]
#[test]
fn fixtures() {
    tracing_subscriber::fmt::try_init();

    let type_error_fixtures = std::fs::read_dir("fixtures/type_errors").unwrap();
    let interpreter_fixtures = std::fs::read_dir("fixtures/interpreter").unwrap();

    let mut failures: Vec<(std::path::PathBuf, String)> = vec![];

    for entry in type_error_fixtures.chain(interpreter_fixtures) {
        let entry = entry.unwrap();
        let path = entry.path();
        println!("Analyzing {}", path.display());

        let file_contents = std::fs::read_to_string(&path).unwrap();
        let (input, expected_output) = file_contents.split_once("\n---\n").unwrap();

        let mut output_writer = vec![];

        let result = {
            let runner = tl::Runner::new(&path, input.to_string(), &mut output_writer);
            runner.and_then(|mut r| r.run("main"))
        };

        if let Ok(result) = result {
            use std::io::Write;

            write!(&mut output_writer, "{}", result).unwrap();
        }

        let actual_output = String::from_utf8(output_writer).unwrap();

        let expected_output = expected_output
            .trim_start_matches('\n')
            .trim_end_matches('\n');
        let actual_output = actual_output
            .trim_start_matches('\n')
            .trim_end_matches('\n');

        if expected_output != actual_output {
            failures.push((path, format!("Test case failed. Input:\n\n{input}\n\nExpected output:\n\n{expected_output}\n\nActual output:\n\n{actual_output}")));
        }
    }

    if !failures.is_empty() {
        for (path, error) in &failures {
            println!("{}:\n{error}", path.display());
        }
        println!("{} failures.", failures.len());
        panic!();
    }
}

#[cfg(test)]
#[test]
fn tests() {
    tracing_subscriber::fmt::try_init();

    let test_fixtures = std::fs::read_dir("fixtures/tests").unwrap();

    let mut num_failures = 0;

    let mut output_writer = vec![];

    for entry in test_fixtures {
        let entry = entry.unwrap();
        let path = entry.path();
        println!("Analyzing {}", path.display());

        let file_contents = std::fs::read_to_string(&path).unwrap();

        let runner = tl::Runner::new(&path, file_contents.to_string(), &mut output_writer);
        match runner {
            Ok(mut runner) => {
                num_failures += runner.run_tests().unwrap();
            }
            Err(_) => {
                std::mem::drop(runner);
                panic!("Error:\n{}", String::from_utf8(output_writer).unwrap());
            }
        }
    }

    if num_failures > 0 {
        println!("{}", String::from_utf8(output_writer).unwrap());
        println!("{} failures.", num_failures);
        panic!();
    }
}
