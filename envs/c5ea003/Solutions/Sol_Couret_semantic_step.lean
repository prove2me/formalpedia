-- Prove2me | solution 1 for Couret.semantic_step
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:12.915484+00:00
-- url     : https://prove2.me/submissions/4880a5b2-651f-4d52-89c5-a4e325f1f39a

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_properSupport_snoc
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









theorem properSupport_singleton (M : CMonoid α) (g u : α) :
    ¬ properSupport M (.snoc .empty g) u := by
  rintro ⟨s, hp, ho, _⟩
  cases s with
  | skip s => cases s; exact hp
  | take s => cases s; exact ho









theorem p2m_local_semantic_step (M : CMonoid α) (w : Word α) (g : α) :
    step M (semanticState M w) g = semanticState M (.snoc w g) := by
  cases w with
  | empty =>
    change State.active g (fun _ => False) =
      State.active (M.mul M.one g) (properSupport M (.snoc .empty g))
    rw [M.one_mul]
    apply congrArg (State.active g)
    funext u
    exact propext ⟨False.elim, properSupport_singleton M g u⟩
  | snoc w a =>
    apply congrArg (State.active (M.mul (total M (.snoc w a)) g))
    funext u
    exact propext (properSupport_snoc M (.snoc w a) True.intro g u).symm



















/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) (w : Couret.Word.{p2m_u_0} α) (g : α),
  @Eq.{p2m_u_0 + 1} (Couret.State.{p2m_u_0} α) (@Couret.step.{p2m_u_0} α M (@Couret.semanticState.{p2m_u_0} α M w) g)
    (@Couret.semanticState.{p2m_u_0} α M (@Couret.Word.snoc.{p2m_u_0} α w g)) := @_root_.Couret.p2m_local_semantic_step

