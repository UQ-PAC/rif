let b64_bytes b = Base64.encode_exn @@ Bytes.to_string @@ b
let flatmap f ls = List.flatten @@ List.map f ls
