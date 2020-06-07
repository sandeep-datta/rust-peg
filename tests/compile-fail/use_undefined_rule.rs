extern crate pegtastic;

pegtastic::parser!(grammar foo() for str {
    rule bar() = foo() //~ ERROR undefined rule `foo`
});

fn main() {}
