use std::collections::BTreeMap;
use std::ops::Add;
use std::rc::{Rc, Weak};

struct Elem<V, W> {
    value: V,
    weight: W,
    pred: Option<Weak<Elem<V, W>>>,
}

struct Tree<V, W> {
    elem: Rc<Elem<V, W>>,
    children: Vec<Tree<V, W>>,
}

pub struct IncrSubseqForest<V, W, F> {
    forest: BTreeMap<V, Tree<V, W>>,
    weight_fn: F,
}

impl<V, W, F> IncrSubseqForest<V, W, F>
where
    V: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    F: FnMut(V) -> W,
{
    pub fn new(weight_fn: F) -> IncrSubseqForest<V, W, F> {
        IncrSubseqForest {
            forest: BTreeMap::new(),
            weight_fn,
        }
    }

    fn first_before(&self, v: V) -> Option<Rc<Elem<V, W>>> {
        self.forest
            .range(..v)
            .next_back()
            .map(|(_, tree)| Rc::clone(&tree.elem))
    }

    fn first_after(&self, v: V) -> Option<Rc<Elem<V, W>>> {
        self.forest
            .range(v..)
            .next()
            .map(|(_, tree)| Rc::clone(&tree.elem))
    }

    fn max_elem(&self) -> Option<Rc<Elem<V, W>>> {
        self.forest
            .iter()
            .next_back()
            .map(|(_, tree)| Rc::clone(&tree.elem))
    }

    pub fn max_weight(&self) -> W {
        self.max_elem().map(|elem| elem.weight).unwrap_or_default()
    }

    pub fn heaviest_seq(&self) -> Vec<V> {
        let mut seq = Vec::new();
        let mut cur_elem = self.max_elem();
        while let Some(elem) = cur_elem {
            seq.push(elem.value);
            cur_elem = elem.pred.as_ref().map(|elem| elem.upgrade().unwrap());
        }
        seq.reverse();
        seq
    }
}

impl<V, W, F> Extend<V> for IncrSubseqForest<V, W, F>
where
    V: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    F: FnMut(V) -> W,
{
    fn extend<S>(&mut self, seq: S)
    where
        S: IntoIterator<Item = V>,
    {
        for cur_val in seq.into_iter() {
            let predecessor = self.first_before(cur_val);
            let prev_weight = predecessor.as_ref().map(|e| e.weight).unwrap_or_default();
            let cur_weight = (self.weight_fn)(cur_val) + prev_weight;

            let mut children = Vec::new();
            while let Some(node) = self.first_after(cur_val) {
                if cur_weight < node.weight {
                    break;
                }
                children.push(self.forest.remove(&node.value).unwrap());
            }

            self.forest.insert(
                cur_val,
                Tree {
                    elem: Rc::new(Elem {
                        value: cur_val,
                        weight: cur_weight,
                        pred: predecessor.as_ref().map(Rc::downgrade),
                    }),
                    children,
                },
            );
        }
    }
}
