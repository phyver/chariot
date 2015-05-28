
let ( @$ ) f x = f x

let  first f (x,y) = (f x, y)
let second f (x,y) = (x, f y)
