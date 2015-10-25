
extern crate rustc_serialize;
extern crate lodestone_simplify;

use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::path::Path;

use lodestone_simplify::{Point, simplify};
use rustc_serialize::json::{self};

#[derive(RustcDecodable)]
struct Points {
  original: Vec<Point>,
  tol5: Vec<Point>
}

#[test]
fn test_simplify() {
  let path = Path::new("tests/points.json");
  let f = File::open(&path).unwrap();
  let mut reader = BufReader::new(f);
  let mut s = String::new();

  reader.read_to_string(&mut s).unwrap();

  let decoded: Points = json::decode(&s).unwrap();
  let simplified = simplify(decoded.original, 5.0, true);

  assert_eq!(simplified.len(), decoded.tol5.len());
  assert_eq!(simplified, decoded.tol5);
}
