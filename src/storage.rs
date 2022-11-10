// Dumb, only entity that knows about files.
pub trait StorageEngine {
    fn get_file_id(table_name: String) -> usize;
    fn read(file_id: usize, page_index: usize) -> Vec<u8>;
}
