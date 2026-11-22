-- Prove2me | solution 1 for Fpy.updates_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:12.758442+00:00
-- url     : https://prove2.me/submissions/3db6f594-5115-4014-b29f-f075f9732a7b

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
theorem _root_.solution {α : Type} {y : Var} :
    ∀ {f : Var → Option α} {ts : List Var} {xs : List α}, y ∉ ts → updates f ts xs y = f y := fun {f} {ts} {xs} h => match f, ts, xs, h with
  | _, [], _, _ | _, _ :: _, [], _ => rfl
  | _, _ :: _, _ :: _, h => by
    rw [updates, solution (List.not_mem_of_not_mem_cons h),
      Function.update_of_ne (List.ne_of_not_mem_cons h)]
end Fpy
