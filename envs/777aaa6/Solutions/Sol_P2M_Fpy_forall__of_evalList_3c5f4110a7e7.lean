-- Prove2me | solution 1 for P2M_Fpy_forall__of_evalList_3c5f4110a7e7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:45.967791+00:00
-- url     : https://prove2.me/submissions/4729ba1d-cbb5-47e3-ad89-b0f4508d516a

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_evalList_vars

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} {ys : List Var} {ns : List Num}
    (h : EvalList Φ σ C (ys.map .var) (ns.map .num)) :
    List.Forall₂ (fun y n => σ y = some (.num n)) ys ns :=
  (List.forall₂_map_right_iff (R := fun y v => σ y = some v) (f := Val.num)).mp (evalList_vars.mp h)
end Fpy
