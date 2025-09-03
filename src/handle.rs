#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Handle(pub(crate) usize);

impl Handle {
    /// Returns the raw numeric identifier for debugging or external maps.
    pub fn as_raw(&self) -> usize {
        self.0
    }
}
