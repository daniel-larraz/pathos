//! Prints what the standard library can tell about standard input, to find
//! out how to recognize what C's `isatty` accepts on Windows (a console or
//! another character device such as NUL) without `unsafe` code. Run by CI
//! on Windows with standard input from NUL, a file and a pipe.

use std::io::IsTerminal;

fn main() {
    let stdin = std::io::stdin();
    println!("is_terminal: {}", stdin.is_terminal());
    #[cfg(windows)]
    {
        use std::io::{Seek, SeekFrom};
        use std::os::windows::io::AsHandle;
        match stdin.as_handle().try_clone_to_owned() {
            Err(e) => println!("clone: {e:?}"),
            Ok(handle) => {
                let mut file = std::fs::File::from(handle);
                match file.metadata() {
                    Ok(m) => println!(
                        "metadata: len {} file {} dir {}",
                        m.len(),
                        m.is_file(),
                        m.is_dir()
                    ),
                    Err(e) => println!("metadata: {e:?}"),
                }
                println!("position: {:?}", file.stream_position());
                println!("seek end: {:?}", file.seek(SeekFrom::End(0)));
                println!("seek start 5: {:?}", file.seek(SeekFrom::Start(5)));
            }
        }
    }
}
