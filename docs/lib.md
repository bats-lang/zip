# lib

### `typedef zip_entry = @{
    name_offset = int,
    name_len = int,
    compression = int,
    compressed_size = int,
    uncompressed_size = int,
    local_header_offset = int
}`

### `fun find_eocd
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n): $R.option(int)`

### `fun parse_eocd
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, eocd_offset: int)
  : @(int, int)`

### `fun parse_cd_entry
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, cd_offset: int)
  : @(zip_entry, int)`

### `fun get_data_offset
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, local_offset: int): $R.option(int)`
