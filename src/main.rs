fn main() {
    let data = include_bytes!("../examples/example.plist");
    let res = bplist::parse(data);

    dbg!(res);
}
