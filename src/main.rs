fn main() {
    if let Some(file_path) = std::env::args().nth(1) {
        let data = std::fs::read(file_path).unwrap();
        dbg!(bplist::parse(&data));
    } else {
    }
}
