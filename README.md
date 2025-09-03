# orderlist
An ordered list that supports stable handles and insertions between elements.


## Example
```rust
use orderlist::{OrderList, Handle};


fn main() {
    let mut numbers = OrderList::new();

    let n1 = numbers.push_back(1);
    let n3 = numbers.push_back(3);
    let n2 = numbers.insert_before(n3, 2).unwrap();
    let n0 = numbers.push_front(0);

}

```

