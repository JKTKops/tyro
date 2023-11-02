(* Utilities for constraint generation. *)
(* Should be easy to instrument this with logging if we want. *)

type 'a free =
  | FOne  of 'a
  | FList of 'a list
  | FCat  of 'a free * 'a free

class recorder = object
  val mutable cstrs : Location.t Ztype.Constraint.t free = FList []
  method emit c =
    cstrs <- FCat (cstrs, FOne c)
  method emit_many cs =
    cstrs <- FCat (cstrs, FList cs)
  method get () =
    let rec go acc = function
      | FOne c -> c :: acc
      | FList cs -> cs @ acc
      | FCat (l, r) -> go (go acc r) l
    in go [] cstrs
end

let recorder_stack = ref [new recorder]

let open_recorder () =
  let r = new recorder in
  recorder_stack := r :: !recorder_stack;
  r
let close_recorder () =
  match !recorder_stack with
  | r::rs ->
    recorder_stack := rs;
    r#get()
  | [] -> failwith "close_recorder: no recorder!"


let current_recorder () =
  match !recorder_stack with
  | [] -> failwith "current_recorder: no recorder!"
  | (r::_) -> r

let emit c = (current_recorder ())#emit c
let emit_many cs = (current_recorder ())#emit_many cs

let listen act =
  let r = open_recorder () in
  let res = act r in
  let cs = close_recorder () in
  res, cs

let get_emitted_constraints () =
  match !recorder_stack with
  | [] -> failwith "Too many close_recorder calls?"
  | [recorder] -> recorder#get ()
  | _ -> failwith "Too few close_recorder calls?"

let reset () = recorder_stack := [new recorder]
