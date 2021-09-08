use heavy_subseq::*;

const MODULUS: usize = (1 << 31) - 1;

struct RandIter {
    cur_rand: usize,
}

impl Iterator for RandIter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let prev_rand = self.cur_rand;
        let new_rand = (16807 * prev_rand + 17) % MODULUS;
        self.cur_rand = new_rand;
        Some(prev_rand)
    }
}

#[test]
fn check_rng() {
    let mut rng = RandIter { cur_rand: 42 };
    assert_eq!(rng.nth(16).unwrap() % 101, 62);

    let mut rng = RandIter { cur_rand: 42 };
    assert_eq!(rng.nth(1024).unwrap() % 101, 0);

    let mut rng = RandIter { cur_rand: 42 };
    assert_eq!(rng.nth(32_768).unwrap() % 101, 35);
}

fn rand_sequence<I: Iterator<Item = usize>>(len: usize, mut rand: I) -> Vec<usize> {
    let mut v = Vec::new();
    v.resize_with(len, || rand.next().unwrap() % len);
    v
}

fn mutation_op(seq: &[usize]) -> Vec<usize> {
    (0..seq.len()).map(|n| seq[seq[n]]).collect()
}

fn sequence_sum(seq: &[usize]) -> usize {
    seq.into_iter().fold(0, |acc, elt| (acc + elt) % 101)
}

#[test]
fn check_rand_sequence() {
    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        sequence_sum(&mutation_op(&rand_sequence(100, rng.skip(100)))),
        77
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        sequence_sum(&mutation_op(&rand_sequence(1000, rng.skip(200)))),
        96
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        sequence_sum(&mutation_op(&rand_sequence(100_982, rng.skip(300)))),
        28
    );
}

#[test]
fn check_incr_subseq_len() {
    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        longest_incr_subseq_len(&rand_sequence(10135, rng.skip(201))) % 101,
        95
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        longest_incr_subseq_len(&rand_sequence(20562, rng.skip(224))) % 101,
        70
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        longest_incr_subseq_len(&rand_sequence(100_123, rng.skip(245))) % 101,
        21
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        longest_incr_subseq_len(&rand_sequence(110_428, rng.skip(289))) % 101,
        37
    );
}

#[test]
fn check_longest_common_subseq_len() {
    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(305_412, rng.skip(732));
    let s2 = mutation_op(&s1);
    assert_eq!(longest_common_subseq_len(&s1, &s2) % 101, 33);

    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(700_320, rng.skip(745));
    let s2 = mutation_op(&s1);
    assert_eq!(longest_common_subseq_len(&s1, &s2) % 101, 16);

    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(1_000_812, rng.skip(763));
    let s2 = mutation_op(&s1);
    assert_eq!(longest_common_subseq_len(&s1, &s2) % 101, 86);
}

fn specialized_his(seq: &[usize]) -> usize {
    let mut already_found_once = vec![false; seq.len()];
    let cost = |_, v| {
        let w = if already_found_once[v] { 3 } else { 1 };
        already_found_once[v] = true;
        w
    };
    heaviest_incr_subseq_weight(seq.iter().copied(), cost)
}

#[test]
fn check_heaviest_incr_subseq_weight() {
    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        specialized_his(&rand_sequence(10_142, rng.skip(401))) % 101,
        85
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        specialized_his(&rand_sequence(20_540, rng.skip(428))) % 101,
        52
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        specialized_his(&rand_sequence(30_489, rng.skip(465))) % 101,
        84
    );
}

fn specialized_hcs(seq1: &[usize], seq2: &[usize]) -> usize {
    let cost = |i, j, _| seq2.len() - if i >= j { i - j } else { j - i };
    heaviest_common_subseq_weight(seq1, seq2, cost)
}

#[test]
fn check_heaviest_common_subseq_weight() {
    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(10_156, rng.skip(809));
    let s2 = mutation_op(&s1);
    assert_eq!(specialized_hcs(&s1, &s2) % 101, 26);

    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(15_129, rng.skip(826));
    let s2 = mutation_op(&s1);
    assert_eq!(specialized_hcs(&s1, &s2) % 101, 9);

    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(17_845, rng.skip(869));
    let s2 = mutation_op(&s1);
    assert_eq!(specialized_hcs(&s1, &s2) % 101, 66);
}

fn specialized_his_min_len(seq: &[usize]) -> usize {
    let mut already_found_once = vec![false; seq.len()];
    let cost = |_, v| {
        let w = if already_found_once[v] { 3 } else { 1 };
        already_found_once[v] = true;
        w
    };
    heaviest_incr_subseq_min_len(seq.iter().copied(), cost)
}

#[test]
fn check_heaviest_incr_subseq_min_len() {
    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        specialized_his_min_len(&rand_sequence(10_378, rng.skip(801))) % 101,
        63
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        specialized_his_min_len(&rand_sequence(20_432, rng.skip(832))) % 101,
        42
    );

    let rng = RandIter { cur_rand: 42 };
    assert_eq!(
        specialized_his_min_len(&rand_sequence(30_654, rng.skip(827))) % 101,
        99
    );
}

fn specialized_hcs_min_len(seq1: &[usize], seq2: &[usize]) -> usize {
    let cost = |i, j, _| seq2.len() - if i >= j { i - j } else { j - i };
    heaviest_common_subseq_min_len(seq1, seq2, cost)
}

#[test]
fn check_heaviest_common_subseq_min_len() {
    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(10_289, rng.skip(804));
    let s2 = mutation_op(&s1);
    assert_eq!(specialized_hcs_min_len(&s1, &s2) % 101, 81);

    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(14_912, rng.skip(823));
    let s2 = mutation_op(&s1);
    assert_eq!(specialized_hcs_min_len(&s1, &s2) % 101, 33);

    let rng = RandIter { cur_rand: 42 };
    let s1 = rand_sequence(18_142, rng.skip(892));
    let s2 = mutation_op(&s1);
    assert_eq!(specialized_hcs_min_len(&s1, &s2) % 101, 61);
}
