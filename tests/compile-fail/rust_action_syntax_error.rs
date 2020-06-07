extern crate pegtastic;

pegtastic::parser!(grammar foo() for str {
    rule foo() = { + } //~ ERROR expected expression, found `+`
});

fn main() {}
