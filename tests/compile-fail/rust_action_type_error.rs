extern crate pegtastic;

struct X;
struct Y;

pegtastic::parser!(grammar foo() for str {
    rule foo() -> X = "a" { Y } //~ ERROR
});

fn main() {}
