-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_substitute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:35.664731+00:00
-- url     : https://prove2.me/submissions/481af9f1-739f-4e69-b384-540e0d2fbe23

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_cons

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n m : ℕ) (f : Images) (w : Word) (hw : ValidWord n w) :
    interpretWord m (substitute f w) =
      FreeGroup.lift (fun i : Fin n => interpretWord m (f.getD i.val [])) (interpretWord n w) := by
  induction w with
  | nil => simp [substitute, interpretWord]
  | cons z w ih =>
    have hz := hw z List.mem_cons_self
    have ht : ValidWord n w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    rw [interpret_cons n z w hz]
    have hs : interpretWord m
        (w.flatMap fun z => if z.2 then f.getD z.1 [] else FreeGroup.invRev (f.getD z.1 [])) =
          FreeGroup.lift (fun i : Fin n => interpretWord m (f.getD i.val [])) (interpretWord n w) := ih ht
    simp only [substitute, List.flatMap_cons, interpret_append, map_mul, hs]
    cases z.2 <;> simp only [Bool.false_eq_true, if_false, if_true,
      interpret_inverse, map_inv, FreeGroup.lift_apply_of]
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
