-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.long_all_scale_lattice_exact
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:52:23.306221+00:00
-- url     : https://prove2.me/submissions/0ca90004-7315-4963-8041-a378d9a0e014

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_finite_window_clears_real_half_height
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_long_all_scale_lattice
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

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

namespace PaperR7
end PaperR7

/-!
# The finite denominator collision bound

Retain membership in the finite pigeonhole box instead of discarding it.
This yields the long paper's literal bound `1 ≤ i < j ≤ D + 1`.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators
open PaperR7

theorem exists_int_sub_of_qsmul_int_bounded {q : ℤ} (hq : 0 < q) (x : ℕ → ℝ)
    (h : ∀ n : ℕ, ∃ k : ℤ, (q : ℝ) * x n = (k : ℝ)) :
    ∃ i j : ℕ, i < j ∧ j ≤ q.toNat ∧ ∃ z : ℤ, x j - x i = (z : ℝ) := by
  classical
  choose k hk using h
  set Q : ℕ := q.toNat with hQ
  have hQpos : 0 < Q := by omega
  have hQcast : ((Q : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq.le
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  have hcard : (Finset.univ : Finset (ZMod Q)).card < (Finset.range (Q + 1)).card := by
    simpa [Finset.card_univ, ZMod.card] using Nat.lt_succ_self Q
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (f := fun n : ℕ => ((k n : ℤ) : ZMod Q)) hcard (fun n _ => Finset.mem_univ _)
  have hiQ : i ≤ Q := by have := Finset.mem_range.mp hi; omega
  have hjQ : j ≤ Q := by have := Finset.mem_range.mp hj; omega
  have hdvd : ∀ u v : ℕ,
      ((k u : ℤ) : ZMod Q) = ((k v : ℤ) : ZMod Q) → (q : ℤ) ∣ k v - k u := by
    intro u v huv
    have hzero : (((k v - k u : ℤ)) : ZMod Q) = 0 := by
      push_cast
      rw [huv]
      ring
    have hd : ((Q : ℕ) : ℤ) ∣ (k v - k u) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    rwa [hQcast] at hd
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have main : ∀ u v : ℕ, (q : ℤ) ∣ k v - k u → ∃ z : ℤ, x v - x u = (z : ℝ) := by
    intro u v hd
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    have hmul : (q : ℝ) * (x v - x u) = (q : ℝ) * (z : ℝ) := by
      rw [mul_sub, hk v, hk u, ← Int.cast_sub, hz]
      push_cast
      ring
    exact mul_left_cancel₀ hqne hmul
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨i, j, hlt, hjQ, main i j (hdvd i j heq)⟩
  · exact ⟨j, i, hlt, hiQ, main j i (hdvd j i heq.symm)⟩
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open PaperR7
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution :
    (∀ u b : ℕ, u ≤ b → ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ)) ∧
    (∀ (N : ℤ) (D : ℕ), 0 < D → paperSeries235 = (N : ℝ) / (D : ℝ) →
      (∀ a : ℕ, 1 ≤ a → ∃ z : ℤ,
        (D : ℝ) * trueNormalizedState a = (z : ℝ)) ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ D + 1 ∧ ∃ z : ℤ,
        trueNormalizedState i - trueNormalizedState j = (z : ℝ)) := by
  refine ⟨finite_window_clears_real_half_height, ?_⟩
  intro N D hD hval
  have hint := (long_all_scale_lattice hD hval).2.1
  refine ⟨hint, ?_⟩
  have hq : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  obtain ⟨i, j, hij, hj, z, hz⟩ := exists_int_sub_of_qsmul_int_bounded hq
    (fun n => trueNormalizedState (1 + n))
    (fun n => by simpa using hint (1 + n) (by omega))
  have hjD : j ≤ D := by simpa using hj
  refine ⟨1 + i, 1 + j, by omega, by omega, by omega, -z, ?_⟩
  rw [Int.cast_neg, ← hz]
  ring
