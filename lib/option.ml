include Stdlib.Option

let get_or s = function Some v -> v | None -> failwith s
