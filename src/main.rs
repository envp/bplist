mod bplist;

use crate::bplist::parser::parse;

fn main() {
    let data = include_bytes!("../empty.plist");
    let _ = parse(data);
}
