

module Term : sig
    type t =
        | Var of string
        | App of t * t
        | Let of string * t * t
        | Fun of string * t
end

module Program : sig
    type t = (string * Term.t) list
end

val dump : Program.t -> unit
