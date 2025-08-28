let b64_bytes b = Base64.encode_exn (Bytes.to_string b)
let bytes_b64 b = Bytes.of_string (Base64.decode_exn b)
let access_index idx l = List.hd (List.filteri (fun i _ -> idx == i) l)
let uncurry f (x, y) = f x y
let compose f g = f @@ g
let second p = match p with _, v -> v
let first p = match p with v, _ -> v
