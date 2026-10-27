#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
#use zip as Z
#target native begin

(* the reader and writer forms: every constructor of the answer and of the fate of each handle is matched *)
fn _reader {start,size_in:nat} (fate: $Z.reader_fate(start, size_in)): int =
  case+ fate of
  | ~$Z.reader_ended(file_read | ) => 1
  | ~$Z.reader_closed_early() => 2
  | ~$Z.reader_lost(failure) => 3

fn _writer (fate: $Z.writer_fate): int =
  case+ fate of
  | ~$Z.writer_held(holds | ) => 1
  | ~$Z.writer_lost(failure) => 2

fn _failure (failure: $Z.inflate_failure): int =
  case+ failure of
  | $Z.failure_malformed() => 1
  | $Z.failure_read() => 2
  | $Z.failure_write() => 3
  | $Z.failure_too_large() => 4

fn _answer {start,size_in:nat} (answer: $Z.inflated(start, size_in)): int =
  case+ answer of
  | ~$Z.inflated_done(inflates, compressed_len, output_len, file_read, holds | size) => size
  | ~$Z.inflated_decoded_unsaved(inflates, file_read | failure) => 0
  | ~$Z.inflated_stopped(failure, reader, writer) => _failure(failure) + _reader(reader) + _writer(writer)

fn _inflate {start,size_in:nat}
  (reader: $F.content_reader($A.cnil(), start, size_in), writer: $F.content_writer($A.cnil()), start: int start, size_in: int size_in): int =
  _answer($Z.inflate_proved(reader, writer, start, size_in))

fn _inflate_stored {start,size_in:nat}
  (reader: $F.content_reader($A.cnil(), start, size_in), writer: $F.content_writer($A.cnil()), start: int start, size_in: int size_in): int =
  _answer($Z.inflate_stored_proved(reader, writer, start, size_in))

end
