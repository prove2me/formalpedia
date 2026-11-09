-- Prove2me | solution 1 for Couret.pickedProduct_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:45:34.186798+00:00
-- url     : https://prove2.me/submissions/229f49f1-1b07-4307-9b19-beacf61c08c2

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

































end Choice

































theorem selectedProduct_positive {w : Word Nat} (s : Choice w) :
    w.atLeastTwo → 0 < Choice.eval natProduct s := by
  induction s with
  | empty => intro _; decide
  | skip s g ih => intro h; exact ih h.1
  | take s g ih =>
    intro h
    exact Nat.mul_pos (ih h.1) (by have hg := h.2; omega)

theorem p2m_local_pickedProduct_gt_one {w : Word Nat} (s : Choice w) :
    w.atLeastTwo → s.picked → 1 < Choice.eval natProduct s := by
  induction s with
  | empty => intro _ h; exact False.elim h
  | skip s g ih => intro h hp; exact ih h.1 hp
  | take s g ih =>
    intro h _
    have hp := selectedProduct_positive s h.1
    have hm := Nat.mul_le_mul_right g (Nat.succ_le_of_lt hp)
    simp only [Nat.one_mul] at hm
    change 1 < Choice.eval natProduct s * g
    have hg := h.2
    omega



/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


theorem solution : ∀ {w : Couret.Word.{0} Nat} (s : @Couret.Choice.{0} Nat w),
  Couret.Word.atLeastTwo w →
    @Couret.Choice.picked.{0} Nat w s →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Couret.Choice.eval.{0} Nat Couret.natProduct w s) := @_root_.Couret.p2m_local_pickedProduct_gt_one

