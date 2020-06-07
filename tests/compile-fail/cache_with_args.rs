extern crate pegtastic;

pegtastic::parser!(grammar foo() for str { 
    #[cache]
    rule foo(x: u32) = "foo" //~ ERROR
});

fn main() {}