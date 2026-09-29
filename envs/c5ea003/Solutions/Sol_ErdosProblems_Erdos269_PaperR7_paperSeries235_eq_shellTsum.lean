-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.paperSeries235_eq_shellTsum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:30:00.284266+00:00
-- url     : https://prove2.me/submissions/57a15386-2326-42d7-af26-194ba5f53e64

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_summable_shellSigma_kernel235
import Theorems.Thm_ErdosProblems_Erdos269_smoothPrefixLcm_eq_threePrimeHeight
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



















theorem smoothReciprocal235_eq_height (x : Smooth235) :
    smoothReciprocal235 x = (threePrimeHeight 2 3 5 x.val : ℝ)⁻¹ := by
  have hx : x.val ≠ 0 := by
    obtain ⟨e, he⟩ := x.property
    rw [← he]
    exact (exponentValue235_pos e).ne'
  unfold smoothReciprocal235
  rw [smoothPrefixLcm_eq_threePrimeHeight
    (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3)
    (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num) (by norm_num) hx]

theorem smoothReciprocal235_comp_exponent (e : Exponent235) :
    smoothReciprocal235 (exponentSmoothEquiv235 e) = exponentKernel235 e := by
  rw [smoothReciprocal235_eq_height]
  rfl

















theorem exponentKernel235_tsum_eq_shellTsum :
    (∑' e : Exponent235, exponentKernel235 e) = dyadicShellTsumTailR235 0 := by
  calc
    (∑' e : Exponent235, exponentKernel235 e) =
        ∑' z : Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a},
          exponentKernel235 z.2.val :=
      (shellExponentEquiv235.tsum_eq exponentKernel235).symm
    _ = ∑' a : ℕ, ∑' e : {e : Exponent235 // e ∈ dyadicSmoothShell235 a},
          exponentKernel235 e.val := summable_shellSigma_kernel235.tsum_sigma
    _ = ∑' a : ℕ, dyadicShellMassR235 a := tsum_congr tsum_exponentKernel235_shell
    _ = dyadicShellTsumTailR235 0 := by simp [dyadicShellTsumTailR235]
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution : paperSeries235 = dyadicShellTsumTailR235 0 := by
  unfold paperSeries235
  calc
    (∑' x : Smooth235, smoothReciprocal235 x) =
        ∑' e : Exponent235, smoothReciprocal235 (exponentSmoothEquiv235 e) :=
      (exponentSmoothEquiv235.tsum_eq smoothReciprocal235).symm
    _ = ∑' e : Exponent235, exponentKernel235 e :=
      tsum_congr smoothReciprocal235_comp_exponent
    _ = dyadicShellTsumTailR235 0 := exponentKernel235_tsum_eq_shellTsum
