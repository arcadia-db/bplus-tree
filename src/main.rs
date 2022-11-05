use bst::bst::BST;
use btree::btree::BPTree;

pub mod bst;
pub mod btree;

fn main() {
    let mut a = BST::new();
    a.insert(5);
    a.insert(3);
    a.insert(6);
    a.insert(2);

    assert_eq!(a.search(7), false);
    assert_eq!(a.search(2), true);
    assert_eq!(a.search(3), true);
    assert_eq!(a.search(1), false);
    assert_eq!(a.search(4), false);
    assert_eq!(a.search(6), true);

    println!("All OK");

    let b: BPTree<i32, String> = BPTree::new();
}
