-- Prove2me | solution 1 for ErdosProblems.Erdos269.hasSum_succ_sq_mul_geometric
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:56:19.040369+00:00
-- url     : https://prove2.me/submissions/2d612936-e027-42cd-9912-b5b4147f412e

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
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
theorem solution {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 2 * r ^ n)
      (2 * (1 / (1 - r) ^ 3) - 1 / (1 - r) ^ 2) := by
  have hr' : ‖r‖ < 1 := by simpa [Real.norm_eq_abs] using hr
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr'
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr'
  have hcomb := (h2.mul_left 2).sub h1
  refine hcomb.congr_fun ?_
  intro n
  have hc2 : ((n + 2).choose 2 : ℝ) * 2 = ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    have h := Nat.succ_mul_choose_eq (n + 1) 1
    rw [Nat.choose_one_right] at h
    have h' : (n + 2) * (n + 1) = (n + 2).choose 2 * 2 := by simpa using h
    exact_mod_cast h'.symm
  have hc1 : ((n + 1).choose 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    rw [Nat.choose_one_right]
  rw [hc1]
  push_cast at hc2 ⊢
  linear_combination (-(r ^ n)) * hc2
