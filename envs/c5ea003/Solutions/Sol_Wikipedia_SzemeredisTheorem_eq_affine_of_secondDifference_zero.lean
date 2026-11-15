-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eq_affine_of_secondDifference_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:56.068358+00:00
-- url     : https://prove2.me/submissions/994668ea-9e26-4e2f-a876-8e414c8fb22c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Unwrapping cyclic progressions in a short interval

A progression obtained by transference lives in `ZMod N`.  The prime weight
is supported on an interval much shorter than a full residue system.  In
that situation the standard representatives have second difference zero
over the integers, so they form an ordinary integer progression.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- A sequence with zero second differences is affine. -/
theorem solution
    (z : ℕ → ℤ) (k : ℕ)
    (hsecond :
      ∀ j : ℕ, j + 2 < k →
        z (j + 2) - 2 * z (j + 1) + z j = 0) :
    ∀ j : ℕ, j < k →
      z j = z 0 + (j : ℤ) * (z 1 - z 0) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      intro
      ring
  | one =>
      intro
      ring
  | more j ihj ihj₁ =>
      intro hj
      have hj₀ : j < k := by omega
      have hj₁ : j + 1 < k := by omega
      have hs := hsecond j hj
      rw [ihj hj₀, ihj₁ hj₁] at hs
      push_cast at hs ⊢
      linarith
