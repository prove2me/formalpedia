-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cyclicAPDiagonalMass_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:31.520505+00:00
-- url     : https://prove2.me/submissions/204e2eca-8a44-40a1-8173-dbf514de983f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators







@[simp]
theorem cyclicAPProduct_zero_difference
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cyclicAPProduct k N f a 0 = f a ^ k := by
  simp [cyclicAPProduct, cyclicAPTerm]

theorem cyclicAPDiagonalMass_eq_sum_pow
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPDiagonalMass k N f = ∑ a : ZMod N, f a ^ k := by
  simp [cyclicAPDiagonalMass]

/-- A pointwise bound `0 ≤ x ≤ B` controls its `k`th power by one copy of
`x` and `k - 1` copies of `B`. -/
theorem pow_le_pow_pred_mul
    {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    x ^ k ≤ B ^ (k - 1) * x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hB0 : 0 ≤ B := hx0.trans hxB
  have hpow : x ^ m ≤ B ^ m :=
    pow_le_pow_left₀ hx0 hxB m
  simpa [Nat.add_comm, pow_succ', Nat.add_sub_cancel, mul_comm] using
    (mul_le_mul_of_nonneg_right hpow hx0)





















end Wikipedia.SzemeredisTheorem

end
/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- The diagonal mass is bounded by the pointwise height to the power
`k-1`, times `N` times the mean.  This is the form used to show that
diagonal progressions are negligible for the W-tricked prime weight. -/
theorem solution
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B) :
    cyclicAPDiagonalMass k N f ≤
      B ^ (k - 1) * (N : ℝ) * mean f := by
  rw [cyclicAPDiagonalMass_eq_sum_pow]
  calc
    ∑ a : ZMod N, f a ^ k ≤
        ∑ a : ZMod N, B ^ (k - 1) * f a := by
      exact Finset.sum_le_sum fun a _ =>
        pow_le_pow_pred_mul (hf0 a) (hfB a) hk
    _ = B ^ (k - 1) * ∑ a : ZMod N, f a := by
      rw [Finset.mul_sum]
    _ = B ^ (k - 1) * ((N : ℝ) * mean f) := by
      rw [← Fintype.card_mul_expect]
      simp [mean, ZMod.card]
    _ = B ^ (k - 1) * (N : ℝ) * mean f := by ring
