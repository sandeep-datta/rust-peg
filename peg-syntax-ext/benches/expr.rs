#![feature(test)]
extern crate peg_syntax_ext;
use peg_syntax_ext::peg;

extern crate test;

use test::Bencher;

peg!(parser r#"
pub expr = eq

#[cache]
eq = additive "=" eq / additive
#[cache]
additive = multitive "+" additive / multitive
#[cache]
multitive = pow "*" multitive / pow
#[cache]
pow = atom "^" pow / atom

#[cache]
atom = [0-9]+ / "(" expr ")"
"#);

#[bench]
fn expr(b: &mut Bencher) {
	let bench_str = "1+2+3+4*5*6^7^8^(0^1*2+1)";

	b.bytes = bench_str.len() as u64;
	b.iter(|| {
		parser::expr(bench_str).unwrap();
	});
}
