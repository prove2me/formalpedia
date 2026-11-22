-- Prove2me | solution 1 for P2M_Fpy_forall__updates_adf16c2a79da
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:39:41.838839+00:00
-- url     : https://prove2.me/submissions/ef0652cd-6007-4693-971d-b020fe73f541

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_updates_of_not_mem

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
theorem _root_.solution {α : Type} :
    ∀ {f : Var → Option α} {ts : List Var} {xs : List α}, ts.Nodup → ts.length = xs.length →
      List.Forall₂ (fun t x => updates f ts xs t = some x) ts xs
  | _, [], [], _, _ => .nil
  | _, _ :: _, _ :: _, h, hl => by
    obtain ⟨ht, hts⟩ := List.nodup_cons.mp h
    exact .cons (by rw [updates, updates_of_not_mem ht, Function.update_self])
      (solution hts (Nat.succ.inj hl))
end Fpy
