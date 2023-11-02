(** Abstract type of environments within Zgen. *)
type t

val empty : t

(** Level management - we're currently ignoring this. *)
val with_new_level : (unit -> 'a) -> 'a

(** Generalize a type in the given environment *)
val generalize : ?name:string
               -> t -> Location.t -> Location.t Ztype.Constraint.t list
               -> Ztype.ztype
               -> Location.t Ztype.Scheme.t

(** Add a value to an environment. *)
val add_value : string -> Location.t Ztype.Scheme.t -> t -> t

(** Lookup a value by its Longident. *)
val lookup_value_by_lident : Longident.t -> t -> Location.t Ztype.Scheme.t

(** Lookup a value by its name as a string. *)
val lookup_value : string -> t -> Location.t Ztype.Scheme.t

(** Extract all the type schemes generated during constraint generation. *)
val get_all_schemes : unit -> Location.t Ztype.Scheme.t list

