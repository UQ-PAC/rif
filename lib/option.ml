include Stdlib.Option

let get_or s (o : 'a option) = Stdlib.Option.value o ~default:(failwith s)
