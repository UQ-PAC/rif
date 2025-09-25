let b64_bytes b = Base64.encode_exn (Bytes.to_string b)
let bytes_b64 b = Bytes.of_string (Base64.decode_exn b)
let access_index idx l = List.hd (List.filteri (fun i _ -> idx == i) l)
let access_primes idx l = snd @@ List.find (fun (i, _) -> i == idx) l
let uncurry f (x, y) = f x y
let compose f g = f @@ g
let contains f l = match List.find_opt f l with Some _ -> true | _ -> false
let ( => ) = fun a b -> (not a) || b
