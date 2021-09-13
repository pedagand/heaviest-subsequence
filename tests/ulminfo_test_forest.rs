mod rng;

use heavy_subseq::common_subseq_forest::{CommonSubseqForest, CommonValue};
use heavy_subseq::incr_subseq_forest::IncrSubseqForest;
use heavy_subseq::max_weight_min_len::add_min_len_goal;
use rng::{gen_sequence, mutation_op, RandomGenerator};

#[test]
fn check_incr_subseq_len() {
    for (l, n, ans) in [
        (10_135, 201, 95),
        (20_562, 224, 70),
        (100_123, 245, 21),
        (110_428, 289, 37),
    ] {
        let rng = RandomGenerator { seed: 42 };
        let mut forest = IncrSubseqForest::new(|_| 1);
        forest.extend(gen_sequence(l, rng.skip(n)));
        assert_eq!(forest.max_weight() % 101, ans);
    }
}

#[test]
fn check_longest_common_subseq_len() {
    for (l, n, ans) in [(305_412, 732, 33), (700_320, 745, 16), (1_000_812, 763, 86)] {
        let rng = RandomGenerator { seed: 42 };
        let seq: Vec<_> = gen_sequence(l, rng.skip(n)).collect();
        let mut forest = CommonSubseqForest::new(seq.iter().copied(), |_| 1);
        forest.extend(mutation_op(&seq));
        assert_eq!(forest.max_weight() % 101, ans);
    }
}

#[test]
fn check_heaviest_incr_subseq_weight() {
    for (l, n, ans) in [(10_142, 401, 85), (20_540, 428, 52), (30_489, 465, 84)] {
        let rng = RandomGenerator { seed: 42 };

        let mut already_found_once = vec![false; l];
        let mut forest = IncrSubseqForest::new(|v| {
            let w = if already_found_once[v] { 3 } else { 1 };
            already_found_once[v] = true;
            w
        });
        forest.extend(gen_sequence(l, rng.skip(n)));
        assert_eq!(forest.max_weight() % 101, ans);
    }
}

#[test]
fn check_heaviest_common_subseq_weight() {
    for (l, n, ans) in [(10_156, 809, 26), (15_129, 826, 9), (17_845, 869, 66)] {
        let rng = RandomGenerator { seed: 42 };
        let seq: Vec<_> = gen_sequence(l, rng.skip(n)).collect();
        let cost = |v: CommonValue<_>| l - if v.i >= v.j { v.i - v.j } else { v.j - v.i };
        let mut forest = CommonSubseqForest::new(seq.iter().copied(), cost);
        forest.extend(mutation_op(&seq));
        assert_eq!(forest.max_weight() % 101, ans);
    }
}

#[test]
fn check_heaviest_incr_subseq_min_len() {
    for (l, n, ans) in [(10_378, 801, 63), (20_432, 832, 42), (30_654, 827, 99)] {
        let rng = RandomGenerator { seed: 42 };

        let mut already_found_once = vec![false; l];
        let mut forest = IncrSubseqForest::new(add_min_len_goal(|v| {
            let w = if already_found_once[v] { 3 } else { 1 };
            already_found_once[v] = true;
            w
        }));
        forest.extend(gen_sequence(l, rng.skip(n)));
        assert_eq!(forest.max_weight().len % 101, ans);
    }
}

#[test]
fn check_heaviest_common_subseq_min_len() {
    for (l, n, ans) in [(10_289, 804, 81), (14_912, 823, 33), (18_142, 892, 61)] {
        let rng = RandomGenerator { seed: 42 };
        let seq: Vec<_> = gen_sequence(l, rng.skip(n)).collect();
        let cost = |v: CommonValue<_>| l - if v.i >= v.j { v.i - v.j } else { v.j - v.i };
        let mut forest = CommonSubseqForest::new(seq.iter().copied(), add_min_len_goal(cost));
        forest.extend(mutation_op(&seq));
        assert_eq!(forest.max_weight().len % 101, ans);
    }
}
