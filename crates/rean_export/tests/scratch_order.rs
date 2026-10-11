#[test]
fn scratch() {
    let m = rean_export::read_module("/private/tmp/claude-501/-Users-david-Desktop-dev-rust-rean/87f3024a-c758-454f-aa27-8597fd9278d0/scratchpad/probe-full.ndjson").unwrap();
    for (i, name) in m.order.iter().enumerate().skip(3198).take(8) {
        let kind = m.env.get(name).map(|d| d.kind_label()).unwrap_or("?");
        println!("OUT {i:5}  {kind:10} {name}");
    }
}
