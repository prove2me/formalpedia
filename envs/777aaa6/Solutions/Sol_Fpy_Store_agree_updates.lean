-- Prove2me | solution 1 for Fpy.Store.agree_updates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:14.629557+00:00
-- url     : https://prove2.me/submissions/f588d32f-2f08-4c06-8921-42fa16eded99

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_Store_agree_update_of_mem


set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
namespace Store
theorem _root_.solution : ∀ (σ : Store) {ts : List Var} (vs : List Val),
    (∀ t ∈ ts, t ∈ X) → σ.Agree X (updates σ ts vs) := fun σ {ts} vs h => match σ, ts, vs, h with
  | _, [], _, _ | _, _ :: _, [], _ => Store.Agree.refl _
  | σ, _ :: _, _ :: _, h => (σ.agree_update_of_mem (h _ (List.mem_cons_self ..)) _).trans
      (solution _ _ fun t ht => h t (List.mem_cons_of_mem _ ht))
end Store
end Fpy
