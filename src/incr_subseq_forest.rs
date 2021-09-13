use std::collections::BTreeMap;
use std::ops::Add;
use std::rc::{Rc, Weak};

pub struct Elem<V, W> {
    value: V,
    weight: W,
    pred: Option<Weak<Elem<V, W>>>,
}

pub struct Tree<V, W> {
    elem: Rc<Elem<V, W>>,
    children: Vec<Tree<V, W>>,
}

impl<V, W> Tree<V, W>
where
    V: Ord,
    W: Ord,
{
    fn new(value: V, weight: W, pred: Option<Rc<Elem<V, W>>>) -> Self {
        Tree {
            elem: Rc::new(Elem {
                value,
                weight,
                pred: pred.as_ref().map(Rc::downgrade),
            }),
            children: Vec::new(),
        }
    }

    fn add_child(&mut self, other_tree: Tree<V, W>) {
        assert!(self.elem.weight >= other_tree.elem.weight);
        assert!(self.elem.value <= other_tree.elem.value);
        self.children.push(other_tree)
    }
}

pub struct GenericIncrSubseqForest<TS, F> {
    forest: TS,
    weight_fn: F,
}

pub trait TreeSet {
    type Value;
    type Weight;

    fn new() -> Self;
    fn first_before(&self, v: Self::Value) -> Option<Rc<Elem<Self::Value, Self::Weight>>>;
    fn first_after(&self, v: Self::Value) -> Option<Rc<Elem<Self::Value, Self::Weight>>>;
    fn max_elem(&self) -> Option<Rc<Elem<Self::Value, Self::Weight>>>;
    fn insert(&mut self, tree: Tree<Self::Value, Self::Weight>);
    fn remove(&mut self, v: Self::Value) -> Tree<Self::Value, Self::Weight>;
}

impl<V, W> TreeSet for BTreeMap<V, Tree<V, W>>
where
    V: Copy + Ord,
    W: Ord,
{
    type Value = V;
    type Weight = W;

    fn new() -> Self {
        BTreeMap::new()
    }

    fn first_before(&self, v: V) -> Option<Rc<Elem<V, W>>> {
        self.range(..v)
            .next_back()
            .map(|(_, tree)| Rc::clone(&tree.elem))
    }

    fn first_after(&self, v: V) -> Option<Rc<Elem<V, W>>> {
        self.range(v..)
            .next()
            .map(|(_, tree)| Rc::clone(&tree.elem))
    }

    fn max_elem(&self) -> Option<Rc<Elem<V, W>>> {
        self.iter()
            .next_back()
            .map(|(_, tree)| Rc::clone(&tree.elem))
    }

    fn insert(&mut self, tree: Tree<V, W>) {
        use std::collections::btree_map::Entry::*;
        match self.entry(tree.elem.value) {
            Vacant(entry) => {
                entry.insert(tree);
            }
            Occupied(mut entry) => entry.get_mut().add_child(tree),
        }
    }

    fn remove(&mut self, v: V) -> Tree<V, W> {
        self.remove(&v).unwrap()
    }
}

pub type IncrSubseqForest<V, W, F> = GenericIncrSubseqForest<BTreeMap<V, Tree<V, W>>, F>;

impl<V, W, F, TS> GenericIncrSubseqForest<TS, F>
where
    V: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    TS: TreeSet<Value = V, Weight = W>,
    F: FnMut(V) -> W,
{
    pub fn new(weight_fn: F) -> Self {
        GenericIncrSubseqForest {
            forest: TS::new(),
            weight_fn,
        }
    }

    pub fn max_weight(&self) -> W {
        self.forest
            .max_elem()
            .map(|elem| elem.weight)
            .unwrap_or_default()
    }

    pub fn heaviest_seq(&self) -> Vec<V> {
        let mut seq = Vec::new();
        let mut cur_elem = self.forest.max_elem();
        while let Some(elem) = cur_elem {
            seq.push(elem.value);
            cur_elem = elem.pred.as_ref().map(|elem| elem.upgrade().unwrap());
        }
        seq.reverse();
        seq
    }
}

impl<V, W, F, TS> Extend<V> for GenericIncrSubseqForest<TS, F>
where
    V: Copy + Ord,
    W: Copy + Ord + Add<Output = W> + Default,
    TS: TreeSet<Value = V, Weight = W>,
    F: FnMut(V) -> W,
{
    fn extend<S>(&mut self, seq: S)
    where
        S: IntoIterator<Item = V>,
    {
        for cur_val in seq.into_iter() {
            let predecessor = self.forest.first_before(cur_val);
            let prev_weight = predecessor.as_ref().map(|e| e.weight).unwrap_or_default();
            let cur_weight = (self.weight_fn)(cur_val) + prev_weight;

            let mut new_tree = Tree::new(cur_val, cur_weight, predecessor);
            while let Some(node) = self.forest.first_after(cur_val) {
                if cur_weight < node.weight {
                    break;
                }
                new_tree.add_child(self.forest.remove(node.value));
            }

            self.forest.insert(new_tree);
        }
    }
}
