let rec even (n : int) =
  if n = 0 then true else if n = -1 then false else odd (n-1)
and     odd  (n : int) = ()

