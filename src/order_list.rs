use crate::{errors::OrderListError, handle::Handle, node::Node};
use core::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};

/// An Order-Maintenance List (OML) with stable handles and fast insert-between.
#[derive(Debug)]
pub struct OrderList<T> {
    nodes: HashMap<usize, Node<T>>,
    order: BTreeMap<u64, usize>,
    next_id: usize,
    head: usize,
    tail: usize,
    len: usize,
}

/// Iterator over values in order.
pub struct Iter<'a, T> {
    inner: std::collections::btree_map::Iter<'a, u64, usize>,
    list: &'a OrderList<T>,
}

/// Iterator over (Handle, &T) in order.
pub struct IterHandles<'a, T> {
    inner: std::collections::btree_map::Iter<'a, u64, usize>,
    list: &'a OrderList<T>,
}

impl<T> Default for OrderList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> OrderList<T> {
    /// Create a new empty list with HEAD(label=0) and TAIL(label=u64::MAX).
    pub fn new() -> Self {
        let mut nodes = HashMap::new();
        let mut order = BTreeMap::new();

        let head_id = 0usize;
        let tail_id = 1usize;

        // Sentinels carry no payload (`value: None`)
        let head = Node {
            id: head_id,
            label: 0,
            prev: None,
            next: Some(tail_id),
            value: None,
        };
        let tail = Node {
            id: tail_id,
            label: u64::MAX,
            prev: Some(head_id),
            next: None,
            value: None,
        };

        nodes.insert(head_id, head);
        nodes.insert(tail_id, tail);
        order.insert(0, head_id);
        order.insert(u64::MAX, tail_id);

        Self {
            nodes,
            order,
            next_id: 2,
            head: head_id,
            tail: tail_id,
            len: 0,
        }
    }

    /// Number of live elements
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is the list empty?
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Push a value to the front (after HEAD).
    pub fn push_front(&mut self, value: T) -> Handle {
        let after_head = Handle(self.head);
        self.insert_after(after_head, value).expect("HEAD is valid")
    }

    /// Push a value to the back (before TAIL).
    pub fn push_back(&mut self, value: T) -> Handle {
        let before_tail = Handle(self.tail);
        self.insert_before(before_tail, value)
            .expect("TAIL is valid")
    }

    /// Insert a value **before** `anchor`. Returns the new element handle.
    ///
    /// Error if `anchor` invalid or is the HEAD sentinel (cannot insert before head).
    pub fn insert_before(&mut self, anchor: Handle, value: T) -> Result<Handle, OrderListError> {
        let anchor_id = self.require_existing(anchor)?;
        if anchor_id == self.head {
            return Err(OrderListError::Sentinel);
        }
        let left_id = self.nodes[&anchor_id]
            .prev
            .expect("non-head anchor must have prev");
        let right_id = anchor_id;
        let label = self.assign_label_between(left_id, right_id);
        Ok(self.insert_between_with_label(left_id, right_id, label, value))
    }

    /// Insert a value **after** `anchor`. Returns the new element handle.
    ///
    /// Error if `anchor` invalid or is the TAIL sentinel (cannot insert after tail).
    pub fn insert_after(&mut self, anchor: Handle, value: T) -> Result<Handle, OrderListError> {
        let anchor_id = self.require_existing(anchor)?;
        if anchor_id == self.tail {
            return Err(OrderListError::Sentinel);
        }
        let left_id = anchor_id;
        let right_id = self.nodes[&anchor_id]
            .next
            .expect("non-tail anchor must have next");
        let label = self.assign_label_between(left_id, right_id);
        Ok(self.insert_between_with_label(left_id, right_id, label, value))
    }

    /// Remove an element by handle, returning its value.
    pub fn remove(&mut self, h: Handle) -> Result<T, OrderListError> {
        let id = self.require_live(h)?;
        let mut node = self.nodes.remove(&id).expect("exists");
        debug_assert!(node.is_live(), "remove called on non-live");

        if let Some(p) = node.prev {
            self.nodes.get_mut(&p).unwrap().next = node.next;
        }
        if let Some(n) = node.next {
            self.nodes.get_mut(&n).unwrap().prev = node.prev;
        }

        self.order.remove(&node.label);

        self.len -= 1;
        Ok(node.value.take().expect("live node has value"))
    }

    /// Compare the **order** of two handles (`Less` means first appears before second).

    pub fn cmp_handles(&self, a: Handle, b: Handle) -> Option<Ordering> {
        let na = self.nodes.get(&a.0)?;
        let nb = self.nodes.get(&b.0)?;
        if !(na.is_live() && nb.is_live()) {
            return None;
        }
        Some(na.label.cmp(&nb.label))
    }

    /// Get a reference by handle (if live).
    pub fn get(&self, h: Handle) -> Option<&T> {
        self.nodes.get(&h.0).and_then(|n| n.value.as_ref())
    }

    /// Get a mutable reference by handle (if live).
    pub fn get_mut(&mut self, h: Handle) -> Option<&mut T> {
        self.nodes.get_mut(&h.0).and_then(|n| n.value.as_mut())
    }

    /// Iterate values in order (by increasing label).
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.order.iter(),
            list: self,
        }
    }

    /// Iterate `(Handle, &T)` in order.
    pub fn iter_handles(&self) -> IterHandles<'_, T> {
        IterHandles {
            inner: self.order.iter(),
            list: self,
        }
    }

    fn require_existing(&self, h: Handle) -> Result<usize, OrderListError> {
        match self.nodes.get(&h.0) {
            Some(n) => Ok(n.id),
            None => Err(OrderListError::InvalidHandle),
        }
    }

    fn require_live(&self, h: Handle) -> Result<usize, OrderListError> {
        match self.nodes.get(&h.0) {
            Some(n) if n.is_live() => Ok(n.id),
            _ => Err(OrderListError::InvalidHandle),
        }
    }

    fn insert_between_with_label(
        &mut self,
        left_id: usize,
        right_id: usize,
        label: u64,
        value: T,
    ) -> Handle {
        let id = self.next_id;
        self.next_id += 1;

        {
            let left = self.nodes.get_mut(&left_id).unwrap();
            debug_assert_eq!(left.next, Some(right_id));
            left.next = Some(id);
        }
        {
            let right = self.nodes.get_mut(&right_id).unwrap();
            right.prev = Some(id);
        }

        let node = Node {
            id,
            label,
            prev: Some(left_id),
            next: Some(right_id),
            value: Some(value),
        };

        self.order.insert(label, id);
        self.nodes.insert(id, node);
        self.len += 1;
        Handle(id)
    }

    fn assign_label_between(&mut self, left_id: usize, right_id: usize) -> u64 {
        let left_lab = self.nodes[&left_id].label;
        let right_lab = self.nodes[&right_id].label;
        if right_lab - left_lab > 1 {
            return left_lab + ((right_lab - left_lab) / 2);
        }
        self.relabel_window(left_id, right_id)
    }

    fn relabel_window(&mut self, mut left: usize, mut right: usize) -> u64 {
        let mut ids = self.collect_span(left, right);

        loop {
            let outer_left = self.nodes[&left].prev.unwrap_or(self.head);
            let outer_right = self.nodes[&right].next.unwrap_or(self.tail);

            let l = self.nodes[&outer_left].label;
            let r = self.nodes[&outer_right].label;

            let need = (ids.len() as u128) + 1;
            let capacity = if r > l { (r - l - 1) as u128 } else { 0 };

            if capacity >= need {
                let step = ((r - l) / ((ids.len() + 1) as u64 + 1)).max(1);
                let mut next_label = l.saturating_add(step);

                for id in &ids {
                    if *id == outer_left || *id == outer_right {
                        continue;
                    }
                    if *id == self.head || *id == self.tail {
                        continue;
                    }
                    let old = self.nodes[id].label;
                    if self.order.remove(&old).is_some() {
                        self.nodes.get_mut(id).unwrap().label = next_label;
                        self.order.insert(next_label, *id);
                    } else {
                        self.nodes.get_mut(id).unwrap().label = next_label;
                        self.order.insert(next_label, *id);
                    }

                    if r - next_label <= step {
                        next_label = next_label.saturating_add(1);
                    } else {
                        next_label = next_label.saturating_add(step);
                    }
                }
                let new_left_lab = self.nodes[&left].label;
                let new_right_lab = self.nodes[&right].label;
                debug_assert!(
                    new_right_lab > new_left_lab,
                    "labels must increase after relabel"
                );
                return new_left_lab + ((new_right_lab - new_left_lab) / 2).max(1);
            }

            if outer_left != self.head {
                left = outer_left;
            }
            if outer_right != self.tail {
                right = outer_right;
            }

            ids = self.collect_span(left, right);

            if left == self.head && right == self.tail {
                return self.global_relabel_and_midpoint();
            }
        }
    }

    fn collect_span(&self, left: usize, right: usize) -> Vec<usize> {
        let mut v = Vec::new();
        let mut cur = Some(left);
        while let Some(id) = cur {
            v.push(id);
            if id == right {
                break;
            }
            cur = self.nodes[&id].next;
        }
        v
    }

    fn global_relabel_and_midpoint(&mut self) -> u64 {
        let total_live = self.len as u128;
        if total_live == 0 {
            return u64::MAX / 2;
        }

        let step: u128 = ((u64::MAX as u128) / (total_live + 1)).max(1);
        let mut i: u128 = 1;

        let keys: Vec<(u64, usize)> = self.order.iter().map(|(k, v)| (*k, *v)).collect();
        for (lab, id) in keys {
            if lab == 0 || lab == u64::MAX {
                continue;
            }
            if !self.nodes[&id].is_live() {
                continue;
            }
            let new_lab = ((step * i) as u64).min(u64::MAX - 1);
            if self.order.remove(&lab).is_some() {
                self.nodes.get_mut(&id).unwrap().label = new_lab;
                self.order.insert(new_lab, id);
            }
            i += 1;
        }

        ((step * ((total_live / 2) + 1)) as u64).clamp(1, u64::MAX - 1)
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        for (_, id) in &mut self.inner {
            let n = &self.list.nodes[id];
            if let Some(v) = n.value.as_ref() {
                if n.label != 0 && n.label != u64::MAX {
                    return Some(v);
                }
            }
        }
        None
    }
}

impl<'a, T> Iterator for IterHandles<'a, T> {
    type Item = (Handle, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        for (_, id) in &mut self.inner {
            let n = &self.list.nodes[id];
            if let Some(v) = n.value.as_ref() {
                if n.label != 0 && n.label != u64::MAX {
                    return Some((Handle(*id), v));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_usage() {
        let mut ol = OrderList::new();
        let a = ol.push_back("A");
        let c = ol.push_back("C");
        let b = ol.insert_before(c, "B").unwrap();

        assert_eq!(ol.iter().cloned().collect::<Vec<_>>(), vec!["A", "B", "C"]);
        assert_eq!(ol.cmp_handles(a, b), Some(Ordering::Less));
        assert_eq!(ol.cmp_handles(c, b), Some(Ordering::Greater));
        assert_eq!(ol.len(), 3);

        // remove
        let v = ol.remove(b).unwrap();
        assert_eq!(v, "B");
        assert_eq!(ol.iter().cloned().collect::<Vec<_>>(), vec!["A", "C"]);
        assert!(ol.get(b).is_none());
        assert_eq!(ol.len(), 2);
    }

    #[test]
    fn many_inserts_between() {
        let mut ol = OrderList::new();
        let a = ol.push_back(0);
        let _z = ol.push_back(999);

        for i in 1..=600 {
            let _ = ol.insert_after(a, i).unwrap();
        }

        let mut expected = Vec::with_capacity(602);
        expected.push(0);
        expected.extend((1..=600).rev());
        expected.push(999);

        let got: Vec<_> = ol.iter().cloned().collect();
        assert_eq!(got, expected, "iteration must reflect maintained order");

        assert_eq!(got.first().copied(), Some(0));
        assert_eq!(got.last().copied(), Some(999));

        let mut last_label = 0u64;
        for (lab, id) in ol.order.iter() {
            if *lab == 0 || *lab == u64::MAX {
                continue;
            }
            assert!(
                *lab > last_label,
                "labels must strictly increase in iteration"
            );
            assert!(ol.nodes[id].is_live());
            last_label = *lab;
        }
    }
}
