#[derive(Debug)]
pub(crate) struct Node<T> {
    pub(crate) id: usize,
    pub(crate) label: u64,
    pub(crate) prev: Option<usize>,
    pub(crate) next: Option<usize>,
    pub(crate) value: Option<T>,
}

impl<T> Node<T> {
    /// Is this node live (not a sentinel / not removed)?
    pub(crate) fn is_live(&self) -> bool {
        self.value.is_some()
    }
}
