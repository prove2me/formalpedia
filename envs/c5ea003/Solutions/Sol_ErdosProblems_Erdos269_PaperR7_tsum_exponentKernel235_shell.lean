-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.tsum_exponentKernel235_shell
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:00:46.459769+00:00
-- url     : https://prove2.me/submissions/96d4ef51-16ae-4241-bfb3-6466ec940033

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Round 7: identify the original smooth-number series with the shell tsum

The distinction is material: a theorem about `dyadicShellTsumTailR235 0` is
not an end-to-end theorem about the paper's `S` until reindexing has been
proved. We build the exponent/smooth-number and shell/exponent equivalences,
prove summability, and identify the literal running-LCM series.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (a : ℕ) :
    (∑' e : {e : Exponent235 // e ∈ dyadicSmoothShell235 a},
      exponentKernel235 e.val) = dyadicShellMassR235 a := by
  rw [tsum_fintype]
  simp only [exponentKernel235, exponentValue235, dyadicShellMassR235,
    dyadicShellMassQ235, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_attach (dyadicSmoothShell235 a)
    (fun e : ℕ × ℕ × ℕ =>
      ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℕ) : ℝ)⁻¹)
