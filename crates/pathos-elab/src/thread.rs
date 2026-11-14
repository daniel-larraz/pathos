//! The thread the checker runs on.
//!
//! Three recursions remain in pathos (see "Recursion deeper than the stack"
//! in `docs/ethos-differences.md`), so how deep a chain of declarations or
//! of includes can be depends on the size of the stack. A process's main
//! thread has 8 MiB on Linux and macOS, subject to `ulimit -s`, and 1 MiB
//! on Windows, where the size is fixed in the executable. The binaries
//! therefore run on a thread of their own whose stack has the same size on
//! every platform.

use std::process::ExitCode;

/// The size of the checker thread's stack: eight times what Ethos's main
/// thread has by default on Linux and macOS. The pages are reserved, and
/// only those the run touches are ever backed by memory.
pub const STACK_BYTES: usize = 64 << 20;

/// Runs `run` on a thread with a stack of [`STACK_BYTES`] and returns its
/// result. The thread is named `main`, so a panic or a stack overflow on it
/// is reported with the words it would have on the main thread, and a panic
/// ends the process with the same status (101).
pub fn on_checker_thread(run: impl FnOnce() -> ExitCode + Send + 'static) -> ExitCode {
    let thread = std::thread::Builder::new()
        .name("main".to_string())
        .stack_size(STACK_BYTES);
    match thread.spawn(run) {
        Ok(handle) => match handle.join() {
            Ok(code) => code,
            // the panic has been reported on the thread
            Err(panic) => std::panic::resume_unwind(panic),
        },
        Err(e) => {
            eprintln!("Error: cannot start the checker's thread: {e}");
            ExitCode::FAILURE
        }
    }
}
