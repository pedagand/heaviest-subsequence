use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::ops::Add;

fn heaviest_incr_subseq_core<S, W, F>(seq: S, mut cost: F) -> (W, Vec<usize>)
where
    S: IntoIterator,
    S::Item: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    F: FnMut(usize, S::Item) -> W,
{
    let mut set = BTreeMap::new();
    let mut pred = Vec::new();
    for (cur_pos, cur_val) in seq.into_iter().enumerate() {
        let pure_weight = cost(cur_pos, cur_val);
        let (prev_weight, prev_pos) = set
            .range(..cur_val)
            .next_back()
            .map(|(_, &(w, i))| (w, Some(i)))
            .unwrap_or((W::default(), None));
        let cur_weight = prev_weight + pure_weight;
        let mut next_pair = set.range(cur_val..).next();
        while let Some((&next_val, &(next_weight, _))) = next_pair {
            if cur_weight < next_weight {
                break;
            }
            set.remove(&next_val);
            next_pair = set.range(cur_val..).next()
        }
        if next_pair.map(|(v, _)| cur_val < *v).unwrap_or(true) {
            set.insert(cur_val, (cur_weight, cur_pos));
        }
        pred.push(prev_pos);
    }
    let (final_weight, mut final_pos) = set
        .values()
        .next_back()
        .map(|&(w, i)| (w, Some(i)))
        .unwrap_or((W::default(), None));
    let mut subseq = vec![];
    while let Some(i) = final_pos {
        subseq.push(i);
        final_pos = pred[i];
    }
    (final_weight, subseq)
}

pub fn heaviest_incr_subseq_weight<S, W, F>(seq: S, cost: F) -> W
where
    S: IntoIterator,
    S::Item: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    F: FnMut(usize, S::Item) -> W,
{
    heaviest_incr_subseq_core(seq, cost).0
}

#[derive(Default, Clone, Copy, Eq, PartialEq)]
struct MaxWeightMinLen<W> {
    weight: W,
    len: usize,
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

pub fn heaviest_incr_subseq_min_len<S, W, F>(seq: S, mut cost: F) -> usize
where
    S: IntoIterator,
    S::Item: Copy + Ord,
    W: Copy + Ord + std::ops::Add<Output = W> + Default,
    F: FnMut(usize, S::Item) -> W,
{
    let len_cost = |i, v| MaxWeightMinLen {
        weight: cost(i, v),
        len: 1,
    };
    heaviest_incr_subseq_core(seq, len_cost).0.len
}

pub fn longest_incr_subseq_len<S>(seq: S) -> usize
where
    S: IntoIterator,
    S::Item: Copy + Ord,
{
    heaviest_incr_subseq_core(seq, |_, _| 1).0
}

fn indices_for_value(sequence: &[usize]) -> Vec<Vec<usize>> {
    let mut result = vec![vec![]; sequence.len()];
    for (pos, &elt) in sequence.iter().enumerate() {
        result[elt].push(pos)
    }
    result
}

use std::cell::Cell;

fn heaviest_common_subseq_core<W, F>(seq1: &[usize], seq2: &[usize], mut cost: F) -> (W, Vec<usize>)
where
    W: Copy + Ord + std::ops::Add<Output = W> + Default,
    F: FnMut(usize, usize, usize) -> W,
{
    let seq2_by_val = indices_for_value(seq2);
    let i = Cell::new(0);
    heaviest_incr_subseq_core(
        seq1.iter().flat_map(|&v| {
            i.set(i.get() + 1);
            seq2_by_val[v].iter().rev().copied()
        }),
        |_, j| cost(i.get() - 1, j, seq2[j]),
    )
}

pub fn heaviest_common_subseq_weight<W, F>(seq1: &[usize], seq2: &[usize], cost: F) -> W
where
    W: Copy + Ord + std::ops::Add<Output = W> + Default,
    F: FnMut(usize, usize, usize) -> W,
{
    heaviest_common_subseq_core(seq1, seq2, cost).0
}

pub fn heaviest_common_subseq_min_len<W, F>(seq1: &[usize], seq2: &[usize], mut cost: F) -> usize
where
    W: Copy + Ord + std::ops::Add<Output = W> + Default,
    F: FnMut(usize, usize, usize) -> W,
{
    let len_cost = |i, j, v| MaxWeightMinLen {
        weight: cost(i, j, v),
        len: 1,
    };
    heaviest_common_subseq_core(seq1, seq2, len_cost).0.len
}

pub fn longest_common_subseq_len(seq1: &[usize], seq2: &[usize]) -> usize {
    heaviest_common_subseq_core(seq1, seq2, |_, _, _| 1).0
}
