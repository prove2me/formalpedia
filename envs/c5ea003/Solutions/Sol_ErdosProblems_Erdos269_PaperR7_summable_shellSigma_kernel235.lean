-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.summable_shellSigma_kernel235
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:28:25.892417+00:00
-- url     : https://prove2.me/submissions/cff6ac34-0063-4a8d-b84e-24679030ea7a

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_tsum_exponentKernel235_shell
import Theorems.Thm_ErdosProblems_Erdos269_summable_dyadicShellMassR235
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
theorem solution :
    Summable (fun z : Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a} =>
      exponentKernel235 z.2.val) := by
  apply (summable_sigma_of_nonneg (fun _ => by
    unfold exponentKernel235
    positivity)).mpr
  constructor
  · intro a
    exact (hasSum_fintype _).summable
  · simpa only [tsum_exponentKernel235_shell] using summable_dyadicShellMassR235
