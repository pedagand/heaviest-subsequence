mod rng;
use rng::*;

#[test]
fn check_rng() {
    for (n, ans) in [(16, 62), (1024, 0), (32_768, 35)] {
        let mut rng = RandomGenerator { seed: 42 };
        assert_eq!(rng.nth(n).unwrap() % 101, ans);
    }
}

#[test]
fn check_rand_sequence() {
    for (l, n, ans) in [(100, 100, 77), (1000, 200, 96), (100_982, 300, 28)] {
        let rng = RandomGenerator { seed: 42 };
        assert_eq!(
            mutation_op(&gen_sequence(l, rng.skip(n)).collect::<Vec<_>>())
                .fold(0, |acc, val| (acc + val) % 101),
            ans
        );
    }
}
