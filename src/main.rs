fn main() {
    let data = include_bytes!("../examples/example.plist");
    let _ = bplist::parse(data);
}
