use crate::incr_subseq_forest::IncrSubseqForest;
use core::cmp::Ordering;
use core::ops::Add;
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
pub struct CommonValue<V> {
    pub i: usize,
    pub j: usize,
    pub value: V,
}

impl<V> Ord for CommonValue<V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.i.cmp(&other.i)
    }
}
impl<V> PartialOrd for CommonValue<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}
impl<V> Eq for CommonValue<V> {}
impl<V> PartialEq for CommonValue<V> {
    fn eq(&self, other: &Self) -> bool {
        self.i == other.i
    }
}

fn indices_by_value<S: IntoIterator>(seq: S) -> BTreeMap<S::Item, Vec<usize>>
where
    S::Item: Ord,
{
    let mut map: BTreeMap<S::Item, Vec<usize>> = BTreeMap::new();
    for (i, val) in seq.into_iter().enumerate() {
        map.entry(val).or_default().push(i)
    }
    map
}

pub struct CommonSubseqForest<V, W, F> {
    forest: IncrSubseqForest<CommonValue<V>, W, F>,
    indices_by_val: BTreeMap<V, Vec<usize>>,
}

impl<V, W, F> CommonSubseqForest<V, W, F>
where
    V: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    F: FnMut(CommonValue<V>) -> W,
{
    pub fn new<S: IntoIterator<Item = V>>(seq: S, weight_fn: F) -> CommonSubseqForest<V, W, F> {
        CommonSubseqForest {
            forest: IncrSubseqForest::new(weight_fn),
            indices_by_val: indices_by_value(seq),
        }
    }

    pub fn max_weight(&self) -> W {
        self.forest.max_weight()
    }

    pub fn heaviest_seq(&self) -> Vec<CommonValue<V>> {
        self.forest.heaviest_seq()
    }
}

impl<V, W, F> Extend<V> for CommonSubseqForest<V, W, F>
where
    V: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    F: FnMut(CommonValue<V>) -> W,
{
    fn extend<S>(&mut self, seq: S)
    where
        S: IntoIterator<Item = V>,
    {
        let indices_by_val = &self.indices_by_val;
        self.forest
            .extend(seq.into_iter().enumerate().flat_map(|(j, value)| {
                indices_by_val
                    .get(&value)
                    .map(|v| v.as_slice())
                    .unwrap_or_else(|| &[][..])
                    .iter()
                    .rev()
                    .map(move |&i| CommonValue { i, j, value })
            }))
    }
}
