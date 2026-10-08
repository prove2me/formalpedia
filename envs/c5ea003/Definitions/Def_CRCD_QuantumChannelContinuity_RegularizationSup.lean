-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationSup
-- name    : CRCD_QuantumChannelContinuity_RegularizationSup
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T22:49:38.110724+00:00
-- url     : https://prove2.me/theorems/7a69445b-19cb-4a1e-b694-14bc6906e3d6
-- title:
--   Supremum identities for extended-valued superadditive sequences
-- statement:
--   Let $f:\mathbb N\to[0,\infty]$ satisfy $f(m)+f(n)\le f(m+n)$ for all natural numbers $m,n$. Then
--
--   $$
--   n f(k)\le f(nk)\quad(n,k\in\mathbb N).
--   $$
--
--   Writing $S(f)=\sup_{k\ge1}f(k)/k$, every integer $n\ge1$ satisfies
--
--   $$
--   \sup_{k\ge1}\frac{f(nk)}k=nS(f).
--   $$
--
--   The denominator on the left is $k$, not $nk$. The same supremum identity holds under the weaker directly supplied repetition premise $n f(k)\le f(nk)$ for all $n,k$, without requiring full superadditivity. Supremum indices exclude zero, and all arithmetic is in the extended nonnegative reals, allowing $f(k)=\infty$ and $S(f)=\infty$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/RegularizationSup.lean#L19-L64

import Mathlib.Data.ENNReal.Inv

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Block suprema on multiples

The regularization identity on positive multiples follows directly from
superadditivity. All operations retain infinite values.
-/

open scoped ENNReal
namespace QuantumChannelContinuity

/-- Repeating a block gives the natural-multiple bound for an extended-real
superadditive sequence, including zero and infinite values. -/
theorem ennreal_nat_mul_le_apply_mul (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) (n k : ℕ) :
    (n : ℝ≥0∞) * f k ≤ f (n * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ((n + 1 : ℕ) : ℝ≥0∞) * f k = (n : ℝ≥0∞) * f k + f k := by
        simp [add_mul]
      _ ≤ f (n * k) + f k := add_le_add ih le_rfl
      _ ≤ f (n * k + k) := hf _ _
      _ = f ((n + 1) * k) := by rw [Nat.add_mul, one_mul]

/-- Exact positive-block scaling of a regularized supremum, using only the
block repetition inequality. No limit or finiteness premise is needed. -/
theorem ennreal_iSup_div_multiples_of_repeat (f : ℕ → ℝ≥0∞)
    (hf : ∀ n k : ℕ, (n : ℝ≥0∞) * f k ≤ f (n * k))
    {n : ℕ} (hn : 0 < n) :
    (⨆ k : ℕ, ⨆ (_ : 0 < k), f (n * k) / (k : ℝ≥0∞)) =
      (n : ℝ≥0∞) * (⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞)) := by
  apply le_antisymm
  · refine iSup_le fun k => iSup_le fun hk => ?_
    have hnk : 0 < n * k := Nat.mul_pos hn hk
    have hbound : f (n * k) / ((n * k : ℕ) : ℝ≥0∞) ≤
        ⨆ j : ℕ, ⨆ (_ : 0 < j), f j / (j : ℝ≥0∞) :=
      le_iSup_of_le (n * k) (le_iSup_of_le hnk le_rfl)
    have hraw := (ENNReal.div_le_iff (by exact_mod_cast hnk.ne')
      (ENNReal.natCast_ne_top (n * k))).mp hbound
    apply (ENNReal.div_le_iff (by exact_mod_cast hk.ne') (by simp)).mpr
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hraw
  · simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun k => iSup_le fun hk => ?_
    apply le_iSup_of_le k
    apply le_iSup_of_le hk
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_right' (hf n k) (k : ℝ≥0∞)⁻¹

/-- A superadditive sequence has the exact regularization scaling on all
positive block multiples. -/
theorem ennreal_iSup_div_multiples (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) {n : ℕ} (hn : 0 < n) :
    (⨆ k : ℕ, ⨆ (_ : 0 < k), f (n * k) / (k : ℝ≥0∞)) =
      (n : ℝ≥0∞) * (⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞)) :=
  ennreal_iSup_div_multiples_of_repeat f (ennreal_nat_mul_le_apply_mul f hf) hn

end QuantumChannelContinuity


