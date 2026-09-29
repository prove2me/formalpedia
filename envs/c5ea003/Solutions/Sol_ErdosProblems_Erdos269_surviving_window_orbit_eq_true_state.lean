-- Prove2me | solution 1 for ErdosProblems.Erdos269.surviving_window_orbit_eq_true_state
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:12:58.799252+00:00
-- url     : https://prove2.me/submissions/3e8a9543-3e76-495b-b8a3-1cd4b19d19b7

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Theorems.Thm_ErdosProblems_Erdos269_dyadicBlockBase235_cases
import Theorems.Thm_ErdosProblems_Erdos269_dyadicNormalizedShellTsumTailR235_succ
import Theorems.Thm_ErdosProblems_Erdos269_dyadicBlockBase235_mem_interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: extinction of the integral branch through pinning windows

The bounded-radix dichotomy leaves exactly one branch between the genuine
infinite tail and cofinal escape: an exact integral normalized state.  This
module lands the structural facts that turn that branch into a decidable,
computationally mapped object.

## 1. Positivity and the pinning identity

Every genuine tail is strictly positive (each shell contains `2^a`).
Unrolling the shell decomposition gives the exact pinning identity

`X_a = d_a / b_a + X_(a+1) / b_a`,

so every true state lies strictly above its window anchor `d_a / b_a`.
In particular, when `b_a` divides `d_a`, the anchor is already an integer
and integrality would force `X_(a+1) = 0`, which positivity forbids: such
scales are killed outright.

## 2. Upward closure

The recurrence has integer coefficients, so one integral state makes every
later state integral.  The integral-index set is empty or a final segment,
so the whole question concentrates on a first integral index.

## 3. Iterated pinning and forced equality

Iterating the pinning identity expresses every true state as a finite
digit sum plus a remainder that carries another factor `2^-k` per shell
(because every block radix is at least two).  Any real orbit following the
recurrence from index `A` onward inside windows of a width function that
reproduces under the recurrence and vanishes against `2^-k` therefore
satisfies `|y_A - X_A| <= width (A+k) / 2^k -> 0`, hence equals the true
state.  Consequently an integer seed surviving all windows forever forces
the true state itself to be integral - exactly the quantity the companion
experiment `check_erdos269_integral_branch.py` measures.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators





theorem dyadicBlockBase235_pos (a : ℕ) : 0 < dyadicBlockBase235 a := by
  rcases dyadicBlockBase235_cases a with h | h | h | h <;>
    simp [h]



















/-! ## Iterated pinning -/



/-! ## Forced equality of window-tracking orbits -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n →
      y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n -
          (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) /
          (dyadicBlockBase235 n : ℝ) + width n)
    (hwidth : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ)
        < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) /
            (dyadicBlockBase235 n : ℝ) + width n)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      width (A + k) / 2 ^ k < ε) :
    y A = trueNormalizedState A := by
  by_contra hne
  have hepos : 0 < |y A - trueNormalizedState A| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  obtain ⟨k₀, hk₀⟩ := hvanish (|y A - trueNormalizedState A| / 2)
    (by linarith [abs_nonneg (y A)])
  -- deviations multiply by at least two per shell
  have hdev : ∀ k : ℕ,
      (2 : ℝ) ^ k * |y A - trueNormalizedState A|
        ≤ |y (A + k) - trueNormalizedState (A + k)| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hbposR : (0 : ℝ) < (dyadicBlockBase235 (A + k) : ℝ) := by
        exact_mod_cast dyadicBlockBase235_pos (A + k)
      have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 (A + k) : ℝ) :=
        mod_cast (dyadicBlockBase235_mem_interval (A + k)).1
      have hts : ∀ n : ℕ, trueNormalizedState n
          = dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 n :=
        fun _ => rfl
      have h1 := hrec (A + k) (by omega)
      have h2 := dyadicNormalizedShellTsumTailR235_succ (A + k)
      have hdiff : y (A + k + 1) - trueNormalizedState (A + k + 1)
          = (dyadicBlockBase235 (A + k) : ℝ)
            * (y (A + k) - trueNormalizedState (A + k)) := by
        rw [h1, hts (A + k + 1), h2, hts (A + k)]
        ring
      have hstep : (2 : ℝ) * |y (A + k) - trueNormalizedState (A + k)|
          ≤ |y (A + k + 1) - trueNormalizedState (A + k + 1)| := by
        rw [hdiff, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rwa [abs_of_pos hbposR]
      calc (2 : ℝ) ^ (k + 1) * |y A - trueNormalizedState A|
          = 2 * ((2 : ℝ) ^ k * |y A - trueNormalizedState A|) := by ring
        _ ≤ 2 * |y (A + k) - trueNormalizedState (A + k)| :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ |y (A + k + 1) - trueNormalizedState (A + k + 1)| := hstep
  -- both orbits sit inside the same window at A + k, so their difference
  -- is at most the width
  have hbound : ∀ k : ℕ,
      |y (A + k) - trueNormalizedState (A + k)| ≤ width (A + k) := by
    intro k
    have hlow : trueNormalizedState (A + k) - y (A + k) ≤ width (A + k) := by
      obtain ⟨hy, hy'⟩ := hwin (A + k) (by omega)
      obtain ⟨hx, hx'⟩ := hwidth (A + k) (by omega)
      linarith
    have hhigh : y (A + k) - trueNormalizedState (A + k) ≤ width (A + k) := by
      obtain ⟨hy, hy'⟩ := hwin (A + k) (by omega)
      obtain ⟨hx, hx'⟩ := hwidth (A + k) (by omega)
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  specialize hk₀ k₀ (Nat.le_refl _)
  have hbound0 := hbound k₀
  have hdev0 := hdev k₀
  -- width (A+k0) < 2^k0 * |e| / 2 while also 2^k0 * |e| <= width
  have hlt : width (A + k₀) / 2 ^ k₀
      < |y A - trueNormalizedState A| / 2 := hk₀
  have hwpos : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  have hcanc : width (A + k₀) / 2 ^ k₀ * 2 ^ k₀ = width (A + k₀) :=
    div_mul_cancel₀ _ hwpos.ne'
  have hm : width (A + k₀) / 2 ^ k₀ * 2 ^ k₀
      < |y A - trueNormalizedState A| / 2 * 2 ^ k₀ :=
    mul_lt_mul_of_pos_right hlt hwpos
  rw [hcanc] at hm
  have hhalf : |y A - trueNormalizedState A| / 2 * 2 ^ k₀
      ≤ |y A - trueNormalizedState A| * 2 ^ k₀ := by
    nlinarith [abs_nonneg (y A - trueNormalizedState A)]
  linarith
