-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.fixed_split_scaled_state_is_integer
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:11:08.327633+00:00
-- url     : https://prove2.me/submissions/77693668-9031-4f93-9a63-dff78ea74afc

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_tail_one_of_paperSeries_eq_rat
import Theorems.Thm_ErdosProblems_Erdos269_qsmul_trueNormalizedState_eq_height_mul_sub
import Theorems.Thm_ErdosProblems_Erdos269_smooth_dvd_heightNormalizer235
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
theorem solution {N : ℤ} {D u v w B a : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ))
    (ha : u + 1 + 2 * v + 3 * w ≤ a) :
    ∃ z : ℤ, (B : ℝ) * trueNormalizedState a = (z : ℝ) := by
  let s : ℕ := 2 ^ u * 3 ^ v * 5 ^ w
  have hspos : 0 < s := by dsimp [s]; positivity
  have hDpos : 0 < D := by rw [hD]; positivity
  have htail := tail_one_of_paperSeries_eq_rat hDpos hval
  have hq : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hDpos
  have htail' : dyadicShellTsumTailR235 1 =
      ((N - (D : ℤ) : ℤ) : ℝ) / ((D : ℤ) : ℝ) := by simpa using htail
  obtain ⟨z, hz⟩ := qsmul_trueNormalizedState_eq_height_mul_sub hq htail'
    (a := a) (by omega)
  obtain ⟨t, ht⟩ := smooth_dvd_heightNormalizer235 (α := u) (β := v) (γ := w) ha
  have hDR : (D : ℝ) = (s : ℝ) * (B : ℝ) := by
    exact_mod_cast hD
  have hHR : (heightNormalizer235 a : ℝ) = (s : ℝ) * (t : ℝ) := by
    exact_mod_cast ht
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast hspos.ne'
  refine ⟨(t : ℤ) * (N - (D : ℤ)) - (B : ℤ) * z, ?_⟩
  apply mul_left_cancel₀ hsne
  calc
    (s : ℝ) * ((B : ℝ) * trueNormalizedState a) =
        (D : ℝ) * trueNormalizedState a := by rw [hDR]; ring
    _ = (heightNormalizer235 a : ℝ) * ((N - (D : ℤ) : ℤ) : ℝ) -
        (D : ℝ) * (z : ℝ) := by simpa using hz
    _ = (s : ℝ) * (((t : ℤ) * (N - (D : ℤ)) - (B : ℤ) * z : ℤ) : ℝ) := by
      rw [hHR, hDR]
      push_cast
      ring
