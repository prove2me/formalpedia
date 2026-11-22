-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.ordinary_word_problem_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:31.093647+00:00
-- url     : https://prove2.me/submissions/f05a0c2e-08fb-4de8-ae15-ee51cdb042c3

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_checkTrivial_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_checkTrivial_correct

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution :
    REPred (fun input : PresentationCode × List (ℕ × Bool) =>
      validInput input ∧
        PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1) := by
  have hp : Partrec (fun input : PresentationCode × List (ℕ × Bool) =>
      Nat.rfind (fun c => (checkTrivial input c : Part Bool))) :=
    Partrec.rfind checkTrivial_primrec.to_comp.partrec.to₂
  apply hp.dom_re.of_eq
  intro input
  rw [Nat.rfind_dom, ← checkTrivial_correct]
  simp
end Kourovka.MetabelianEnumeration.ComputablePresentations
