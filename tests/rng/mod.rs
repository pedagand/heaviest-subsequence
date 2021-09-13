const MODULUS: usize = (1 << 31) - 1;

pub struct RandomGenerator {
    pub seed: usize,
}

impl Iterator for RandomGenerator {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let prev_rand = self.seed;
        let new_rand = (16807 * prev_rand + 17) % MODULUS;
        self.seed = new_rand;
        Some(prev_rand)
    }
}

pub fn gen_sequence<I: Iterator<Item = usize>>(
    len: usize,
    source: I,
) -> impl Iterator<Item = usize> {
    source.take(len).map(move |v| v % len)
}

pub fn mutation_op<'a>(seq: &'a [usize]) -> impl 'a + Iterator<Item = usize> {
    (0..seq.len()).map(move |n| seq[seq[n]])
}
