-- Prove2me | solution 1 for Couret.fullSupport_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:23.706195+00:00
-- url     : https://prove2.me/submissions/881bd607-822f-4685-bace-a15b62525c77

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_Choice_eval_allSkip
import Theorems.Thm_Couret_Choice_eval_of_not_omitted
import Theorems.Thm_Couret_Choice_eval_of_not_picked
import Std

/-!
COU-87, first semantic formalization, 2026-10-30.
The denotation uses independent choices of labeled occurrences, not the automaton
recurrence. Snoc words make appending an occurrence explicit. No assumption of
distinct factors is made. This file does not certify the 147/101 finite tables.
-/

universe u
namespace Couret





variable {α : Type u}







namespace Choice













theorem eval_allTake (M : CMonoid α) (w : Word α) :
    eval M (allTake w) = total M w := by
  induction w with
  | empty => rfl
  | snoc w g ih => exact congrArg (fun x => M.mul x g) ih



















end Choice





theorem p2m_local_fullSupport_iff (M : CMonoid α) (w : Word α) (u : α) :
    fullSupport M w u ↔ properSupport M w u ∨ u = M.one ∨ u = total M w := by
  constructor
  · rintro ⟨s, hu⟩
    by_cases hp : s.picked
    · by_cases ho : s.omitted
      · exact Or.inl ⟨s, hp, ho, hu⟩
      · exact Or.inr (Or.inr (hu.symm.trans (Choice.eval_of_not_omitted M s ho)))
    · exact Or.inr (Or.inl (hu.symm.trans (Choice.eval_of_not_picked M s hp)))
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨s, _, _, hu⟩; exact ⟨s, hu⟩
    · exact ⟨Choice.allSkip w, (Choice.eval_allSkip M w).trans h.symm⟩
    · exact ⟨Choice.allTake w, (Choice.eval_allTake M w).trans h.symm⟩

































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) (w : Couret.Word.{p2m_u_0} α) (u : α),
  Iff (@Couret.fullSupport.{p2m_u_0} α M w u)
    (Or (@Couret.properSupport.{p2m_u_0} α M w u)
      (Or (@Eq.{p2m_u_0 + 1} α u (@Couret.CMonoid.one.{p2m_u_0} α M))
        (@Eq.{p2m_u_0 + 1} α u (@Couret.total.{p2m_u_0} α M w)))) := @_root_.Couret.p2m_local_fullSupport_iff

