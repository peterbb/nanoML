
module type OP = sig
    type t
    val eq : t -> t -> bool
end

module type VAR = sig
    type t
    val fresh : unit -> t
    val eq : t -> t -> bool
end

module Var : VAR

module type LANG = sig
    module O : OP
    module V : VAR

    type t =
        | Var of V.t
        | App of O.t * t list
end

module MakeLang : functor (O : OP) ->
      LANG with module O = O
           with module V = Var

module Make : functor (L : LANG) -> sig
    type var
    type t

    val true_ : t
    val and_  : t -> t -> t
    val eq_   : L.t -> L.t -> t
    val ex_   : (L.t -> t) -> t
    val def_  : L.t -> (var -> t) -> t
    val let_  : (L.t -> t) -> (var -> t) -> t
    val app_  : var -> L.t -> t

    type subst = (L.V.t * L.t) list
    val solve : t -> ((subst * L.V.t list), string) result
end
