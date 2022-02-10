use bplist::parser::parse;

fn main() {
    let data = include_bytes!("../examples/example.plist");
    let _ = parse(data);
}
