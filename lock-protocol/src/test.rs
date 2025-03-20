
pub type Paddr = usize;

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub pa: Paddr,
    pub flags: PteFlag,

    pub level: usize, // this should not be here, just for testing
    pub children: Paddr, // this should not be here, just for testing
    // pub children_index: usize, // this should not be here, just for testing
}

fn main() {
    println!("size of PageTableEntry: {}", core::mem::size_of::<PageTableEntry>());

    use std::collections::HashMap;

    let map = HashMap::from([
        ("a", 1),
        ("b", 2),
        ("c", 3),
    ]);

    for key in map.keys() {
        println!("{key}");
    }
    let keys = map.keys();
    println!("{:?}", keys);
}