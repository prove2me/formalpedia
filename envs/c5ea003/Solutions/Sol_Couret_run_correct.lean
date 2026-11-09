-- Prove2me | solution 1 for Couret.run_correct
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:33.872543+00:00
-- url     : https://prove2.me/submissions/e8e0d3b9-8420-42ce-a1c3-c28b6a77d10e

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_semantic_step
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

































end Choice























theorem p2m_local_run_correct (M : CMonoid α) (w : Word α) :
    run M w = semanticState M w := by
  induction w with
  | empty => rfl
  | snoc w g ih =>
    change step M (run M w) g = semanticState M (.snoc w g)
    rw [ih]
    exact semantic_step M w g















/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) (w : Couret.Word.{p2m_u_0} α),
  @Eq.{p2m_u_0 + 1} (Couret.State.{p2m_u_0} α) (@Couret.run.{p2m_u_0} α M w) (@Couret.semanticState.{p2m_u_0} α M w) := @_root_.Couret.p2m_local_run_correct

