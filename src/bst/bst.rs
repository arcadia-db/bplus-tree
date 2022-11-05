#[derive(Debug)]
struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
    val: i32,
}

impl Node {
    pub fn new(val: i32) -> Node {
        Node {
            left: None,
            right: None,
            val,
        }
    }

    pub fn insert(&mut self, val: i32) {
        if val < self.val {
            match &mut self.left {
                None => {
                    self.left = Some(Box::new(Node::new(val)));
                }
                Some(x) => {
                    x.insert(val);
                }
            }
        } else if val > self.val {
            match &mut self.right {
                None => {
                    self.right = Some(Box::new(Node::new(val)));
                }
                Some(x) => {
                    x.insert(val);
                }
            }
        }
    }

    pub fn search(&self, val: i32) -> bool {
        if val < self.val {
            match &self.left {
                None => false,
                Some(x) => x.search(val),
            }
        } else if val > self.val {
            match &self.right {
                None => false,
                Some(x) => x.search(val),
            }
        } else {
            true
        }
    }
}

pub struct BST {
    root: Option<Box<Node>>,
}

impl BST {
    pub fn new() -> BST {
        BST { root: None }
    }

    pub fn insert(&mut self, val: i32) {
        match &mut self.root {
            None => {
                self.root = Some(Box::new(Node::new(val)));
            }
            Some(x) => {
                x.insert(val);
            }
        }
    }

    pub fn search(&self, val: i32) -> bool {
        match &self.root {
            None => false,
            Some(x) => x.search(val),
        }
    }
}
