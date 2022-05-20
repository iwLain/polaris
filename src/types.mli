open Ast
open NameExpr

module Subst : sig
    type t
end

type tc_env

val typecheck : expr list -> ty

