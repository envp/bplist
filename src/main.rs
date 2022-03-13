fn main() {
    // let data = include_bytes!("../examples/example.plist");
    let data = include_bytes!("/Library/Preferences/com.apple.Bluetooth.plist");
    let _ = dbg!(bplist::parse(data));
}
