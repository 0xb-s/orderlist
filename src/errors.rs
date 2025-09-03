/// Errors that can occur when operating on the list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderListError {
    InvalidHandle,

    Sentinel,
}
impl core::fmt::Display for OrderListError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.clone() {
            OrderListError::InvalidHandle => f.write_str("invalid handle"),
            OrderListError::Sentinel => f.write_str("cannot insert relative to sentinel"),
        }
    }
}
impl std::error::Error for OrderListError {}
