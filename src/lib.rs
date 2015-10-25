
use std::collections::BTreeSet;
use std::ops::{Add, Mul, Sub};

extern crate rustc_serialize;

use rustc_serialize::{Decoder, Decodable};
use rustc_serialize::json::{Json, ToJson};

#[derive(Debug, Clone, Copy)]
pub struct Point {
  pub x: f64,
  pub y: f64
}

pub fn simplify(
    points: Vec<Point>,
    tolerance: f64,
    hq: bool) -> Vec<Point> {

  let sq_tolerance = tolerance * tolerance;
  let pts = if hq { points } else { simplify_radial_distance(points, sq_tolerance) };

  simplify_douglas_peucker(pts, sq_tolerance)
}

impl ToJson for Point {
  fn to_json(&self) -> Json {
    Json::Array(vec![self.x.to_json(), self.y.to_json()])
  }
}

impl Decodable for Point {
  fn decode<D: Decoder>(d: &mut D) -> Result<Point, D::Error> {
    d.read_seq(|decoder, len| {
      if len != 2 {
        let msg = format!("Expecting array of length: {}, but found {}", 2, len);
        panic!(msg);
      }

      let point = Point {
        x: try!(decoder.read_seq_elt(0, Decodable::decode)),
        y: try!(decoder.read_seq_elt(1, Decodable::decode))
      };
        
      Ok(point)
    })
  }
}

impl PartialEq for Point {
  fn eq(&self, other: &Self) -> bool {
    self.x == other.x && self.y == other.y
  }
}

impl Add for Point {
  type Output = Point;
  fn add(self, other: Self) -> Self {
    let x = self.x + other.x;
    let y = self.y + other.y;
    Point{x: x, y: y}
  }
}

impl Mul for Point {
  type Output = Point;
  fn mul(self, other: Self) -> Self {
    let x = self.x * other.x;
    let y = self.y * other.y;
    Point{x: x, y: y}
  }
}

impl Sub for Point {
  type Output = Point;
  fn sub(self, other: Self) -> Self {
    let x = self.x - other.x;
    let y = self.y - other.y;
    Point{x: x, y: y}
  } 
}

impl Point {
  pub fn sq_dist(&self, other: &Self) -> f64 {
    let dx = self.x - other.x;
    let dy = self.x - other.y;
    dx * dx + dy * dy  
  }
}

/// http://paulbourke.net/geometry/pointlineplane/
///
/// ## Parameters
/// * pt - standalone point
/// * pt1 - Line segment endpoint
/// * pt2 - Line segment endpoint
fn get_square_segment_distance(p: Point, p1: Point, p2: Point) -> f64 {
  let mut x = p1.x;
  let mut y = p1.y;
  let mut dx = p2.x - x;
  let mut dy = p2.y - y;

  if dx != 0.0 || dy != 0.0 {
    let t = ((p.x - x) * dx + (p.y - y) * dy) / (dx * dx + dy * dy);
    if t > 1.0 {
      x = p2.x;
      y = p2.y;
    } else if t > 0.0 {
      x += dx * t;
      y += dy * t;
    }
  }

  dx = p.x - x;
  dy = p.y - y;
  dx * dx + dy * dy
}

/// Basic distance-based simplification
fn simplify_radial_distance(
    points: Vec<Point>,
    sq_tolerance: f64) -> Vec<Point> {

  let last = points.last().unwrap().clone();
  let mut prev = points.first().unwrap();
  let mut new_points = vec![prev.clone()];
  let mut iter = points.iter();

  iter.next(); // skip the first point
  for point in points.iter() {
    if point.sq_dist(prev) > sq_tolerance {
      new_points.push(point.clone());
      prev = point;
    }
  }

  if prev.clone() != last {
    new_points.push(last);
  }

  new_points
}

fn simplify_douglas_peucker(
    points: Vec<Point>,
    sq_tolerance: f64) -> Vec<Point> {

  let len = points.len();
  let mut first = 0;
  let mut last = len - 1;
  let mut pair = (first, last);
  let mut markers = BTreeSet::new();
  let mut stack: Vec<(usize, usize)> = vec![];
  let mut index = 0;

  // keep first and last indices..
  markers.insert(first);
  markers.insert(last);

  loop {
    let mut max_sq_dist = 0.0;

    first = pair.0;
    last = pair.1;

    for i in first+1..last {
      let pt1 = points[i];
      let sq_dist = get_square_segment_distance(pt1, points[first], points[last]);

      if sq_dist > max_sq_dist {
        index = i;
        max_sq_dist = sq_dist;
      }
    }

    if max_sq_dist > sq_tolerance {
      markers.insert(index);
      stack.push((first, index));
      stack.push((index, last));
    }

    match stack.pop() {
      Some(p) => pair = p,
      None => break
    }
  }

  markers.iter().map(|&i| points[i]).collect()
}

#[cfg(test)]
mod tests {
  use super::{
    Point,
    get_square_segment_distance,
    simplify_radial_distance,
    simplify_douglas_peucker
  };

  #[test]
  fn test_add() {
    let pt1 = Point{x: 2.0, y: 2.0};
    let pt2 = Point{x: 1.0, y: 1.0};
    let pt3 = Point{x: 1.0, y: 1.0};

    assert_eq!(pt1 + pt2, Point{x: 3.0, y: 3.0});
    assert_eq!(pt2 + pt3, Point{x: 2.0, y: 2.0});
  }

  #[test]
  fn test_mul() {
    let pt1 = Point{x: 4.0, y: 4.0};
    let pt2 = Point{x: 2.0, y: 2.0};
    let pt3 = Point{x: 1.0, y: 1.0};

    assert_eq!(pt1 * pt2, Point{x: 8.0, y: 8.0});
    assert_eq!(pt2 * pt3, Point{x: 2.0, y: 2.0});
  }

  #[test]
  fn test_sub() {
    let pt1 = Point{x: 2.0, y: 2.0};
    let pt2 = Point{x: 1.0, y: 1.0};
    let pt3 = Point{x: 1.0, y: 1.0};

    assert_eq!(pt1 - pt2, Point{x: 1.0, y: 1.0});
    assert_eq!(pt2 - pt3, Point{x: 0.0, y: 0.0});
    assert_eq!(pt2 - pt1, Point{x: -1.0, y: -1.0});
  }

  #[test]
  fn test_get_square_segment_distance() {
    let pt1 = Point{x: 2.0, y: 2.0};
    let pt2 = Point{x: 0.0, y: 0.0};
    let pt3 = Point{x: 4.0, y: 0.0};
    let pt4 = Point{x: 4.0, y: 4.0};

    let pt5 = Point{x: 224.55, y: 250.15};
    let pt6 = Point{x: 866.36, y: 480.77};
    let pt7 = Point{x: 784.20, y: 218.16};
    let pt8 = Point{x: 779.60, y: 216.87};

    assert_eq!(get_square_segment_distance(pt1, pt2, pt3), 4.0);
    assert_eq!(get_square_segment_distance(pt1, pt2, pt4), 0.0);
    assert_eq!(get_square_segment_distance(pt7, pt5, pt6), 48117.146246042365);
    assert_eq!(get_square_segment_distance(pt8, pt5, pt6), 47967.43057247439);
  }

  #[test]
  fn test_simplify_radial_distance() {
    let pt1 = Point{x: 0.0, y: 0.0};
    let pt2 = Point{x: 1.0, y: 1.0};
    let pt3 = Point{x: 2.0, y: 2.0};
    let pt4 = Point{x: 3.0, y: 3.0};
    let pt5 = Point{x: 4.0, y: 4.0};
    
    let points = vec![pt1, pt2, pt3, pt4, pt5];
    let sq_tolerance = 4.0;
    let expected = vec![pt1, pt3, pt5];

    assert_eq!(expected, simplify_radial_distance(points, sq_tolerance));
  }

  #[test]
  fn test_simplify_douglas_peucker() {
    let pt1 = Point{x: 0.0, y: 0.0};
    let pt2 = Point{x: 1.0, y: 1.0};
    let pt3 = Point{x: 2.0, y: 2.0};
    let pt4 = Point{x: 3.0, y: 3.0};
    let pt5 = Point{x: 4.0, y: 4.0};

    let points = vec![pt1, pt2, pt3, pt4, pt5];
    let sq_tolerance = 4.0;
    let expected = vec![pt1, pt5];

    assert_eq!(expected, simplify_douglas_peucker(points, sq_tolerance));
  }
}
