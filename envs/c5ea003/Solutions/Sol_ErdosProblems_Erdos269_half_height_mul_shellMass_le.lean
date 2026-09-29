-- Prove2me | solution 1 for ErdosProblems.Erdos269.half_height_mul_shellMass_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:15:55.254734+00:00
-- url     : https://prove2.me/submissions/d69fc168-974e-47bc-b6be-b1a2b09689e8

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellMassR235_nonneg
import Theorems.Thm_ErdosProblems_Erdos269_prod_dyadicBlockBase235_ge_two_pow
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_pow_add_eq_mul_prod
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
theorem solution (m n : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)
      ≤ (dyadicOrderedBlockDigit235 (m + n) : ℝ) / 2 ^ (n + 1) := by
  have hdigit : (threePrimeHeight 2 3 5 (2 ^ (m + n + 1)) : ℝ) / 2
      * dyadicShellMassR235 (m + n) = (dyadicOrderedBlockDigit235 (m + n) : ℝ) :=
    half_threePrimeHeight_mul_dyadicShellMassR235 (m + n)
  have hH : (threePrimeHeight 2 3 5 (2 ^ (m + (n + 1))) : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ m) : ℝ)
        * ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
    threePrimeHeight235_pow_add_eq_mul_prod m (n + 1)
  have hP : (2 : ℝ) ^ (n + 1)
      ≤ ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
    prod_dyadicBlockBase235_ge_two_pow m (n + 1)
  have hPpos : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) :=
    lt_of_lt_of_le (by positivity) hP
  have hHm : (0 : ℝ) < (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) :=
    threePrimeHeight235_cast_pos _
  have hmass : 0 ≤ dyadicShellMassR235 (m + n) := dyadicShellMassR235_nonneg _
  have hidx : m + n + 1 = m + (n + 1) := Nat.add_assoc m n 1
  rw [hidx] at hdigit
  -- `(H_m/2) · mass = digit / P` with `P ≥ 2^(n+1)`
  have hkey : (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellMassR235 (m + n)
      = (dyadicOrderedBlockDigit235 (m + n) : ℝ)
        / ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (m + j) : ℝ) := by
    rw [eq_div_iff hPpos.ne', ← hdigit, hH]
    ring
  rw [hkey]
  have hd : (0 : ℝ) ≤ (dyadicOrderedBlockDigit235 (m + n) : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_left hd (by positivity) hP
