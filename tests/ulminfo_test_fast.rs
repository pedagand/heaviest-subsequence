mod rng;

use heavy_subseq::fast::*;
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
        assert_eq!(
            longest_incr_subseq_len(gen_sequence(l, rng.skip(n))) % 101,
            ans
        );
    }
}

#[test]
fn check_longest_common_subseq_len() {
    for (l, n, ans) in [(305_412, 732, 33), (700_320, 745, 16), (1_000_812, 763, 86)] {
        let rng = RandomGenerator { seed: 42 };
        let s1: Vec<_> = gen_sequence(l, rng.skip(n)).collect();
        let s2: Vec<_> = mutation_op(&s1).collect();
        assert_eq!(longest_common_subseq_len(&s1, &s2) % 101, ans);
    }
}

#[test]
fn check_heaviest_incr_subseq_weight() {
    for (l, n, ans) in [(10_142, 401, 85), (20_540, 428, 52), (30_489, 465, 84)] {
        let rng = RandomGenerator { seed: 42 };

        let mut already_found_once = vec![false; l];
        let cost = |_, v| {
            let w = if already_found_once[v] { 3 } else { 1 };
            already_found_once[v] = true;
            w
        };

        assert_eq!(
            heaviest_incr_subseq_weight(gen_sequence(l, rng.skip(n)), cost) % 101,
            ans
        );
    }
}

#[test]
fn check_heaviest_common_subseq_weight() {
    for (l, n, ans) in [(10_156, 809, 26), (15_129, 826, 9), (17_845, 869, 66)] {
        let rng = RandomGenerator { seed: 42 };
        let s1: Vec<_> = gen_sequence(l, rng.skip(n)).collect();
        let s2: Vec<_> = mutation_op(&s1).collect();
        let cost = |i, j, _| l - if i >= j { i - j } else { j - i };
        assert_eq!(heaviest_common_subseq_weight(&s1, &s2, cost) % 101, ans);
    }
}

#[test]
fn check_heaviest_incr_subseq_min_len() {
    for (l, n, ans) in [(10_378, 801, 63), (20_432, 832, 42), (30_654, 827, 99)] {
        let rng = RandomGenerator { seed: 42 };

        let mut already_found_once = vec![false; l];
        let cost = |_, v| {
            let w = if already_found_once[v] { 3 } else { 1 };
            already_found_once[v] = true;
            w
        };

        assert_eq!(
            heaviest_incr_subseq_min_len(gen_sequence(l, rng.skip(n)), cost) % 101,
            ans
        );
    }
}

#[test]
fn check_heaviest_common_subseq_min_len() {
    for (l, n, ans) in [(10_289, 804, 81), (14_912, 823, 33), (18_142, 892, 61)] {
        let rng = RandomGenerator { seed: 42 };
        let s1: Vec<_> = gen_sequence(l, rng.skip(n)).collect();
        let s2: Vec<_> = mutation_op(&s1).collect();
        let cost = |i, j, _| l - if i >= j { i - j } else { j - i };
        assert_eq!(heaviest_common_subseq_min_len(&s1, &s2, cost) % 101, ans);
    }
}
