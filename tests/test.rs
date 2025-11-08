#[cfg(test)]
#[test]
fn fixtures() {
    let _ = tracing_subscriber::fmt::try_init();

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
            let runner = tl::Runner::new(&path, input.to_string(), None, &mut output_writer);
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
    use tracing::debug;

    let _ = tracing_subscriber::fmt::try_init();

    let test_fixtures = std::fs::read_dir("fixtures/tests").unwrap();
    let lib_test_fixtures = std::fs::read_dir("fixtures/lib").unwrap();

    let mut num_failures = 0;
    let mut num_passes = 0;
    let mut failing_tests = vec![];

    let mut output_writer = vec![];

    let test_file_filter = std::env::var("TL_TEST_FILE");
    let test_name_filter = std::env::var("TL_TEST_NAME").ok();

    for entry in test_fixtures.chain(lib_test_fixtures) {
        let entry = entry.unwrap();
        let path = entry.path();

        if let Ok(filter) = test_file_filter.as_ref() {
            if let Some(path_str) = path.to_str() {
                if !path_str.contains(filter.as_str()) {
                    debug!("Skipping test {path_str} due to filter {filter}");
                    continue;
                }
            }
        }

        println!("Analyzing {}", path.display());

        let file_contents = std::fs::read_to_string(&path).unwrap();

        let runner = tl::Runner::new(
            &path,
            file_contents.to_string(),
            test_name_filter.clone(),
            &mut output_writer,
        );
        match runner {
            Ok(mut runner) => {
                let failures = runner.run_tests().unwrap();
                if failures > 0 {
                    num_failures += runner.run_tests().unwrap();
                    failing_tests.push(path.display().to_string());
                } else {
                    num_passes += 1;
                }
            }
            Err(ref error) => {
                let error = format!("{:?}", error);
                std::mem::drop(runner);
                panic!(
                    "Error: {error}\n{}",
                    String::from_utf8(output_writer).unwrap()
                );
            }
        }
    }

    if num_failures > 0 {
        println!("{}", String::from_utf8(output_writer).unwrap());
        println!("{num_failures} failures: {failing_tests:?}");
        panic!();
    }
    eprintln!("{num_passes} passing test files");
}
