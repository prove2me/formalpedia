-- Prove2me | solution 1 for Couret.Choice.eval_of_not_omitted
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:31.150205+00:00
-- url     : https://prove2.me/submissions/7aa3e4e2-8f84-4f69-9b84-8ddff4c0af1d

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





















theorem p2m_local_eval_of_not_omitted (M : CMonoid α) {w : Word α} (s : Choice w) :
    ¬ omitted s → eval M s = total M w := by
  induction s with
  | empty => intro _; rfl
  | skip s g ih => intro h; exact False.elim (h True.intro)
  | take s g ih => intro h; exact congrArg (fun x => M.mul x g) (ih h)











end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) {w : Couret.Word.{p2m_u_0} α} (s : @Couret.Choice.{p2m_u_0} α w),
  Not (@Couret.Choice.omitted.{p2m_u_0} α w s) →
    @Eq.{p2m_u_0 + 1} α (@Couret.Choice.eval.{p2m_u_0} α M w s) (@Couret.total.{p2m_u_0} α M w) := @_root_.Couret.Choice.p2m_local_eval_of_not_omitted

