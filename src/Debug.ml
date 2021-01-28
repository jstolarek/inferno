let enabled     = false
let hard        = true
let print_ranks = true
let print_repr  = false
let fuel        = 8

let print_str message =
  if enabled then prerr_endline message;
  flush stderr

let print doc =
  if enabled then
    PPrint.(ToChannel.pretty 0.9 80 stderr (doc ^^ hardline));
  flush stderr

(* Only enabled detailed debuf if debug enabled *)
let hard = enabled && hard
