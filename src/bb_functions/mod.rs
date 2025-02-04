//! Logic to convert **all** basic blocks (BB) to functions.
//!
//! This is pretty tricky, as this is the overall setup:
//! - Identify all reads/writes to variables for all BBs that make up a given function.
//! - For each variable that is not defined within the BB (and is also not a static/const/etc.), add it as a parameter to the function.
//! - For each of these parameters, also infer it's type and use this as an arg (not as bad as this sounds).
//! - For each of these BBs that have a terminator of a `JUMP` to one of the function's BB, replace it with a `CALL` to the generated function instead.
//! - Reconstruct all BB statements to refer to the function argument instead of the original variable (hard??).
//!

mod bb_read_write_scan;
