
module Type : sig
    type t =
        | Var   of int
        | Arrow of t * t
end

type var
type t

val true_ : t
val and_  : t -> t -> t
val eq_   : Type.t -> Type.t -> t
val ex_   : (Type.t -> t) -> t
val def_  : Type.t -> (var -> t) -> t
val let_  : (Type.t -> t) -> (var -> t) -> t
val app_  : var -> Type.t -> t

type subst = (int * Type.t) list
val solve : t -> ((subst * int list), string) result
