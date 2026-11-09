-- Prove2me | solution 1 for Couret.Choice.eval_allSkip
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:36.641726+00:00
-- url     : https://prove2.me/submissions/5d83d39b-84fc-40b0-aa8c-e2d7cb43ec7a

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
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











theorem p2m_local_eval_allSkip (M : CMonoid α) (w : Word α) :
    eval M (allSkip w) = M.one := by
  induction w with
  | empty => rfl
  | snoc w g ih => exact ih





















end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) (w : Couret.Word.{p2m_u_0} α),
  @Eq.{p2m_u_0 + 1} α (@Couret.Choice.eval.{p2m_u_0} α M w (@Couret.Choice.allSkip.{p2m_u_0} α w))
    (@Couret.CMonoid.one.{p2m_u_0} α M) := @_root_.Couret.Choice.p2m_local_eval_allSkip

