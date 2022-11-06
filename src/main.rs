use bst::bst::BST;
use btree::btree::BPTree;

pub mod bst;
pub mod btree;

fn main() {
    let mut a = BST::new();
    a.insert(5);
    a.insert(3);
    a.insert(6);
    // a.insert(2);

    // assert_eq!(a.search(7), false);
    // assert_eq!(a.search(2), true);
    // assert_eq!(a.search(3), true);
    // assert_eq!(a.search(1), false);
    // assert_eq!(a.search(4), false);
    // assert_eq!(a.search(6), true);

    // println!("All OK");

    // let mut bptree: BPTree<i32, String, 3> = BPTree::new();
    // bptree.insert(&3, &String::from("Emily"));
    // bptree.insert(&5, &String::from("Srihari"));

    // // update value of 5
    // bptree.insert(&5, &String::from("Cool"));

    // // this should trigger a leaf split, and create a new root node
    // bptree.insert(&7, &String::from("Rajat"));
    // println!("{:#?}", bptree);
    // let res = bptree.search(&7).unwrap();
    // let lock = res.read().unwrap();
    // drop(lock);
}
