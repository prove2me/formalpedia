-- Prove2me | solution 1 for Fpy.evalList_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:32:04.266757+00:00
-- url     : https://prove2.me/submissions/1f1c40e0-4fa9-4dd4-807f-facedf33b9db

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} : ∀ {ys : List Var} {vs : List Val},
    EvalList Φ σ C (ys.map .var) vs ↔ List.Forall₂ (fun y v => σ y = some v) ys vs
  | [], _ => ⟨fun h => by cases h; exact .nil, fun h => by cases h; exact .nil⟩
  | _ :: _, _ =>
    ⟨fun h => by
      cases h with
      | cons hv hs => cases hv with
        | var hx => exact .cons hx ((solution).mp hs),
     fun h => by
      cases h with
      | cons hx hs => exact .cons (.var hx) ((solution).mpr hs)⟩
end Fpy
