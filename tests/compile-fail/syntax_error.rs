extern crate pegtastic;

pegtastic::parser!(grammar foo() for str {
    fn asdf() {} //~ ERROR expected one of "#", "crate", "pub", "rule", "use", "}"
});

fn main() {}
