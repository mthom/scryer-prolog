use scryer_prolog::machine::Machine;
use serde_json;

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn lib_integration_test() {
    let mut machine = Machine::new_lib();

    // File with test commands, i.e. program code to consult and queries to run
    let code = include_str!("./lib_integration_test_commands.txt");

    // Split the code into blocks
    let blocks = code.split("=====");

    let mut i = 0;
    let mut last_result: Option<_> = None;
    // Iterate over the blocks
    for block in blocks {
        // Trim the block to remove any leading or trailing whitespace
        let block = block.trim();

        // Skip empty blocks
        if block.is_empty() {
            continue;
        }

        // Check if the block is a query
        if let Some(query) = block.strip_prefix("query") {
            // Parse and execute the query
            let result = machine.run_query(query.to_string());
            assert!(result.is_ok());

            last_result = Some(result);
        } else if let Some(code) = block.strip_prefix("consult") {
            // Load the code into the machine
            machine.consult_module_string("facts", code.to_string());
        } else if let Some(result) = block.strip_prefix("result") {
            i += 1;
            if let Some(Ok(ref last_result)) = last_result {
                let last_result_str = serde_json::to_string(last_result).unwrap();
                //println!("\n\n=====Result No. {i}=======\n{last_result}\n===============");
                println!("=====Result No. {i}=======");
                println!("{last_result_str}");
                println!("===============");
                println!();
                assert_eq!(last_result_str, result.to_string().trim());
            }
        }
    }
}
