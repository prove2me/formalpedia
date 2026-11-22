-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.recursively_enumerable_of_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:59:46.868436+00:00
-- url     : https://prove2.me/submissions/2d737f57-0fc6-48d7-b9b6-c57af305b0c7

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution
    (check : ℕ → ℕ → Bool) (hc : Computable₂ check) (P : ℕ → Prop)
    (correct : ∀ p, P p ↔ ∃ c, check p c = true) : REPred P := by
  have hp : Partrec (fun p => Nat.rfind (fun c => (check p c : Part Bool))) :=
    Partrec.rfind hc.partrec.to₂
  apply hp.dom_re.of_eq
  intro p
  rw [Nat.rfind_dom, correct]
  simp
end Kourovka.MetabelianEnumeration
