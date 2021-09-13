use core::cmp::Ordering;
use std::ops::Add;

#[derive(Default, Clone, Copy, Eq, PartialEq)]
pub struct MaxWeightMinLen<W> {
    pub weight: W,
    pub len: usize,
}

impl<W: Add<Output = W>> Add for MaxWeightMinLen<W> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        MaxWeightMinLen {
            weight: self.weight + rhs.weight,
            len: self.len + rhs.len,
        }
    }
}

impl<W: Ord> PartialOrd for MaxWeightMinLen<W> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<W: Ord> Ord for MaxWeightMinLen<W> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight
            .cmp(&other.weight)
            .then_with(|| self.len.cmp(&other.len).reverse())
    }
}

pub fn add_min_len_goal<V, W, F>(mut weight_fn: F) -> impl FnMut(V) -> MaxWeightMinLen<W>
where
    F: FnMut(V) -> W,
{
    move |v| MaxWeightMinLen {
        weight: weight_fn(v),
        len: 1,
    }
}
