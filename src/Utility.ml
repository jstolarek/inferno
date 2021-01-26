let rec unduplicate equal = function
  | [] -> []
  | elem :: elems -> (let _, others = List.partition (equal elem) elems in
                      elem :: unduplicate equal others)

let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1
