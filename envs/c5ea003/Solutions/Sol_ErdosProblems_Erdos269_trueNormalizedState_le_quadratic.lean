-- Prove2me | solution 1 for ErdosProblems.Erdos269.trueNormalizedState_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:32:11.702814+00:00
-- url     : https://prove2.me/submissions/76840bff-51a8-404b-82f5-b7011d7e75ea

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Theorems.Thm_ErdosProblems_Erdos269_dyadicOrderedBlockDigit235_le_quadratic
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellMassR235_nonneg
import Theorems.Thm_ErdosProblems_Erdos269_summable_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_hasSum_succ_sq_div_two_pow
import Theorems.Thm_ErdosProblems_Erdos269_half_height_mul_shellMass_le
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
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
# Erdős #269: an explicit all-scale width for the normalized tail state

The genuine half-height normalized tail state
`X_a = trueNormalizedState a = (H(2^a)/2) · Σ_{h ≥ 2^a} 1/H(h)`
is the state whose integrality the `B = 1` corner asks about, and whose
`q`-multiples the rationality lattice makes integral.  Every consumer of the
integral branch (`IntegralRigidity`, the local-window residue consumer of
`RestrictedFloorSum`) needs an explicit all-scale enclosure `0 < X_a ≤ W(a)`.
Positivity is `trueNormalizedState_pos`; this module supplies the width.

The bound is the poly-geometric tsum estimate.  Writing the tail from scale
`m` shell by shell,

`X_m = Σ_{n ≥ 0} d_(m+n) / (b_m ⋯ b_(m+n))`

with the ordered digit `d_a = dyadicOrderedBlockDigit235 a ≤ 15 (a+1)^2` and
every radix `b ≥ 2`, so

`X_m ≤ Σ_{n ≥ 0} 15 (m+n+1)^2 / 2^(n+1) ≤ 15 (m+1)^2 Σ_{n ≥ 0} (n+1)^2 / 2^(n+1)
     = 90 (m+1)^2`,

using `(m+n+1) ≤ (m+1)(n+1)` and the exact value
`Σ_{n ≥ 0} (n+1)^2 r^n = 2/(1-r)^3 - 1/(1-r)^2`, which at `r = 1/2` is `12`.

The main theorem is `trueNormalizedState_le_quadratic`; the cubic corollary
`trueNormalizedState_le_cubic` is the form recorded in the longitudinal record.
The measured constant is `sup_a X_a/(a+1)^2 ≈ 0.91` (attained at `a = 0`), so
the bound is crude by about two orders of magnitude and can be sharpened with a
sharper digit majorant; nothing downstream needs more than an explicit
polynomial.

No rationality hypothesis is used.  Erdős #269 remains open.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (m : ℕ) :
    trueNormalizedState m ≤ 90 * ((m + 1 : ℕ) : ℝ) ^ 2 := by
  -- the state is the tsum of the half-height-normalized shells
  have hsum : Summable (fun n : ℕ => dyadicShellMassR235 (m + n)) :=
    summable_dyadicShellMassR235.comp_injective fun _ _ h => Nat.add_left_cancel h
  have hstate : trueNormalizedState m
      = ∑' n : ℕ, (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n) := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235 dyadicShellTsumTailR235
    rw [tsum_mul_left]
  -- the majorant `15 (m+1)^2 (n+1)^2 / 2^(n+1)` and its exact sum
  have hmaj : HasSum
      (fun n : ℕ => 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n)
        / 2)
      (15 * ((m + 1 : ℕ) : ℝ) ^ 2 * 12 / 2) := by
    have := (hasSum_succ_sq_div_two_pow.mul_left (15 * ((m + 1 : ℕ) : ℝ) ^ 2)).div_const 2
    simpa using this
  have hle : ∀ n : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)
        ≤ 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) / 2 := by
    intro n
    refine (half_height_mul_shellMass_le m n).trans ?_
    have hd : (dyadicOrderedBlockDigit235 (m + n) : ℝ) ≤ 15 * ((m + n + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic (m + n)
    have hsplit : ((m + n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : ((m + n + 1 : ℕ) : ℝ) ^ 2 ≤ (((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hsplit 2
    have hR : 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) / 2
        = 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (n + 1) := by
      rw [one_div_pow, pow_succ]
      field_simp
      ring
    rw [hR]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc (dyadicOrderedBlockDigit235 (m + n) : ℝ) ≤ 15 * ((m + n + 1 : ℕ) : ℝ) ^ 2 := hd
      _ ≤ 15 * (((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith [hsq]
      _ = 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
  have hnonneg : ∀ n : ℕ,
      0 ≤ (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n) := by
    intro n
    exact mul_nonneg (by positivity) (dyadicShellMassR235_nonneg _)
  have hsumL : Summable (fun n : ℕ =>
      (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)) :=
    hsum.mul_left _
  rw [hstate]
  calc (∑' n : ℕ, (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n))
      ≤ ∑' n : ℕ, 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n) / 2 :=
        hsumL.tsum_le_tsum hle hmaj.summable
    _ = 15 * ((m + 1 : ℕ) : ℝ) ^ 2 * 12 / 2 := hmaj.tsum_eq
    _ = 90 * ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
