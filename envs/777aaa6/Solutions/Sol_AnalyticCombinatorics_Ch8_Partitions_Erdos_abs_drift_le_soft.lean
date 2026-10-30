-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le_soft
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:02:47.618139+00:00
-- url     : https://prove2.me/submissions/a1fc4eea-08b8-428e-bb33-152d2da2341d

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SoftTailDrift
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Soft-tail Tanaka drift bound

The banked `abs_drift_le` needs a *global* hard increment bound (`K x z ≠ 0 → |D z − D x| ≤ b`).
The Erdős predecessor kernel only has *soft* far tails: most mass moves by `≤ b`, but a small
`farMass` moves further (up to the range `2R`).  This lemma charges that far mass to an additive
error: the one-step `|D|`-drift is `≤ b + 2R·farMass`, where

  `farMass K D b x = ∑_z K x z · 1[|D z − D x| > b]`.

Telescoped, this turns the Tanaka occupation bound into
`window-occupation ≥ (E|D_T| − E|D_0| − ηT − 2R·∑_t farMass_t)/b`, so a per-step far mass summing to
`o(√T)` over the horizon leaves the `√T` Paley–Zygmund signal intact.  Deterministic finite-sum.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ)
theorem solution (b R : ℝ) (x : ι) (hbnn : 0 ≤ b)
    (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1) (hR : ∀ z, |D z| ≤ R) :
    (∑ z, K x z * |D z|) ≤ |D x| + b + 2 * R * farMass K D b x := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR x)
  have hstep : ∀ z ∈ (Finset.univ : Finset ι),
      K x z * |D z| ≤ K x z * (|D x| + b) + 2 * R * (K x z * (if |D z - D x| ≤ b then (0:ℝ) else 1)) := by
    intro z _
    by_cases hnear : |D z - D x| ≤ b
    · rw [if_pos hnear, mul_zero, mul_zero, add_zero]
      refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
      calc |D z| = |D x + (D z - D x)| := by congr 1; ring
        _ ≤ |D x| + |D z - D x| := abs_add_le _ _
        _ ≤ |D x| + b := by linarith [hnear]
    · rw [if_neg hnear, mul_one]
      have hbound : |D z| ≤ |D x| + b + 2 * R := by
        calc |D z| ≤ R := hR z
          _ ≤ |D x| + b + 2 * R := by linarith [abs_nonneg (D x)]
      calc K x z * |D z| ≤ K x z * (|D x| + b + 2 * R) :=
            mul_le_mul_of_nonneg_left hbound (hKnn z)
        _ = K x z * (|D x| + b) + 2 * R * K x z := by ring
  calc (∑ z, K x z * |D z|)
      ≤ ∑ z, (K x z * (|D x| + b)
          + 2 * R * (K x z * (if |D z - D x| ≤ b then (0:ℝ) else 1))) :=
        Finset.sum_le_sum hstep
    _ = (∑ z, K x z * (|D x| + b))
          + 2 * R * (∑ z, K x z * (if |D z - D x| ≤ b then (0:ℝ) else 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = |D x| + b + 2 * R * farMass K D b x := by
        rw [← Finset.sum_mul, hKsum, one_mul, farMass]
