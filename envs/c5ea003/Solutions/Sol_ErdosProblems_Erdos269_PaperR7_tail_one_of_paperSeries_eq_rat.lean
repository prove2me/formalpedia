-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.tail_one_of_paperSeries_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:47:48.862979+00:00
-- url     : https://prove2.me/submissions/0fb2eb31-1aba-40f5-9065-cbd9cb00aa47

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
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_paperSeries235_eq_shellTsum
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellTsumTailR235_zero_eq
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
# Round 7: the fixed denominator split and the literal original value

The existing bridge existentially chooses a split and a carry. The paper fixes
`D = 2^u 3^v 5^w B`, fixes the onset, and identifies that carry with `B X_a`.
This file proves those equality data rather than citing a nearby existential.
The long-record sharper `Q`-cap remains a separate obligation.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution {N : ℤ} {D : ℕ} (hD : 0 < D)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    dyadicShellTsumTailR235 1 = ((N - (D : ℤ) : ℤ) : ℝ) / (D : ℝ) := by
  have h := hval
  rw [paperSeries235_eq_shellTsum, dyadicShellTsumTailR235_zero_eq] at h
  have hDn : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  calc
    dyadicShellTsumTailR235 1 = (N : ℝ) / (D : ℝ) - 1 := by linarith
    _ = ((N - (D : ℤ) : ℤ) : ℝ) / (D : ℝ) := by
      push_cast
      field_simp <;> ring
