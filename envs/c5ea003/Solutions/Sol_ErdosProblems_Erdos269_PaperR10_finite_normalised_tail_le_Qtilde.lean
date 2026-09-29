-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.finite_normalised_tail_le_Qtilde
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:03:54.544384+00:00
-- url     : https://prove2.me/submissions/fa4de458-8f5e-47cf-9fc4-7344aa2ff33e

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Definitions.Def_ErdosProblems_Erdos269_PaperR8RankMajorant
import Definitions.Def_ErdosProblems_Erdos269_ActualSharpTailMajorantR10
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_height_growth_sharp_dyadic
import Theorems.Thm_ErdosProblems_Erdos269_hasSum_succ_sq_mul_geometric
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_hasSum_rankMajorant
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_heightRank235_dyadic
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_heightRank235_mono
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_rank_fibre_card_bound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# The jump-constrained bound for the literal tail

The extra growth is proved directly for the three floor logarithms. This avoids
assuming an enumeration of the jump word or an unproved majorisation supplier.
At a dyadic starting point, d₂ ≤ 2d₃+1. Consequently the first k rank increases
multiply the height by at least 2^(k-j)3^j, j=(k+1)/3. The residue-three sum
then gives precisely the printed Q̃, with the existing actual rank-fibre bound.


-/

namespace ErdosProblems.Erdos269.PaperR10
open scoped BigOperators
open PaperR7 PaperR8



theorem sharpJumpDenom_pos (k : ℕ) : 0 < sharpJumpDenom k := by
  unfold sharpJumpDenom
  positivity

theorem two_pow_le_sharpJumpDenom (k : ℕ) : 2 ^ k ≤ sharpJumpDenom k := by
  have hj : (k + 1) / 3 ≤ k := by omega
  have hk : k = (k - (k + 1) / 3) + (k + 1) / 3 := by omega
  calc
    2 ^ k = 2 ^ (k - (k + 1) / 3) * 2 ^ ((k + 1) / 3) := by
      conv_lhs => rw [hk]
      rw [pow_add]
    _ ≤ sharpJumpDenom k := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _)





theorem sharpJumpDenom_residues (m : ℕ) :
    sharpJumpDenom (3 * m) = 12 ^ m ∧
    sharpJumpDenom (3 * m + 1) = 2 * 12 ^ m ∧
    sharpJumpDenom (3 * m + 2) = 6 * 12 ^ m := by
  have h0 : (3 * m + 1) / 3 = m := by omega
  have h1 : (3 * m + 1 + 1) / 3 = m := by omega
  have h2 : (3 * m + 2 + 1) / 3 = m + 1 := by omega
  have e0 : 3 * m - m = 2 * m := by omega
  have e1 : 3 * m + 1 - m = 2 * m + 1 := by omega
  have e2 : 3 * m + 2 - (m + 1) = 2 * m + 1 := by omega
  have hp : 2 ^ (2 * m) * 3 ^ m = 12 ^ m := by
    rw [pow_mul, ← mul_pow]
    norm_num
  constructor
  · simp only [sharpJumpDenom, h0, e0, hp]
  constructor
  · simp only [sharpJumpDenom, h1, e1, pow_add, pow_one]
    nlinarith [hp]
  · simp only [sharpJumpDenom, h2, e2, pow_add, pow_one]
    nlinarith [hp]



theorem sharpRankMajorant_nonneg (n k : ℕ) : 0 ≤ sharpRankMajorant n k := by
  unfold sharpRankMajorant
  positivity

theorem sharpRankMajorant_le_rankMajorant (n k : ℕ) :
    sharpRankMajorant n k ≤ rankMajorant n k := by
  have hd : (2 : ℝ) ^ k ≤ (sharpJumpDenom k : ℝ) := by
    exact_mod_cast two_pow_le_sharpJumpDenom k
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    (by positivity : (0 : ℝ) < 18 * 2 ^ k) (mul_le_mul_of_nonneg_left hd (by norm_num))

theorem summable_sharpRankMajorant (n : ℕ) : Summable (sharpRankMajorant n) :=
  Summable.of_nonneg_of_le (sharpRankMajorant_nonneg n)
    (sharpRankMajorant_le_rankMajorant n) (hasSum_rankMajorant n).summable



theorem sharpRankMajorant_group (n m : ℕ) :
    (∑ r : Fin 3, sharpRankMajorant n (3 * m + r.val)) =
      (15 * ((m + 1 : ℕ) : ℝ) ^ 2 + (10 * (n : ℝ) + 5) * (m + 1) +
        (10 * (n : ℝ) ^ 2 + 10 * n + 7) / 6) * (1 / 12 : ℝ) ^ m / 18 := by
  have hd := sharpJumpDenom_residues m
  simp [Fin.sum_univ_succ, sharpRankMajorant, hd.1, hd.2.1, hd.2.2]
  push_cast
  field_simp
  <;> ring

theorem hasSum_sharpRankMajorant (n : ℕ) :
    HasSum (sharpRankMajorant n) (carryMajorantQtilde n : ℝ) := by
  have hg0 := hasSum_choose_mul_geometric_of_norm_lt_one 0
    (by norm_num : ‖(1 / 12 : ℝ)‖ < 1)
  have hg1 := hasSum_choose_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1 / 12 : ℝ)‖ < 1)
  have h0 : HasSum (fun m : ℕ => (1 / 12 : ℝ) ^ m) (12 / 11) := by
    norm_num at hg0
    exact hg0
  have h1 : HasSum (fun m : ℕ => ((m + 1 : ℕ) : ℝ) * (1 / 12 : ℝ) ^ m)
      (144 / 121) := by
    convert hg1 using 1 <;> norm_num [Nat.choose_one_right]
  have h2 : HasSum (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / 12 : ℝ) ^ m)
      (1872 / 1331) := by
    convert hasSum_succ_sq_mul_geometric
      (by norm_num : |(1 / 12 : ℝ)| < 1) using 1 <;> norm_num
  have hh := (((h2.mul_left 15).add (h1.mul_left (10 * (n : ℝ) + 5))).add
    (h0.mul_left ((10 * (n : ℝ) ^ 2 + 10 * n + 7) / 6))).div_const 18
  have hval : (15 * (1872 / 1331 : ℝ) + (10 * (n : ℝ) + 5) * (144 / 121) +
      ((10 * (n : ℝ) ^ 2 + 10 * n + 7) / 6) * (12 / 11)) / 18 =
      (carryMajorantQtilde n : ℝ) := by
    simp only [carryMajorantQtilde, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
    ring
  rw [hval] at hh
  have hgroup : HasSum (fun m : ℕ => ∑ r : Fin 3,
      sharpRankMajorant n (3 * m + r.val)) (carryMajorantQtilde n : ℝ) := by
    apply hh.congr_fun
    intro m
    rw [sharpRankMajorant_group]
    push_cast
    ring
  have hs := summable_sharpRankMajorant n
  have hp : Summable (fun z : ℕ × Fin 3 => sharpRankMajorant n (3 * z.1 + z.2.val)) :=
    hs.comp_injective rankResidueEquiv.symm.injective
  have heq : (∑' k : ℕ, sharpRankMajorant n k) =
      ∑' m : ℕ, ∑ r : Fin 3, sharpRankMajorant n (3 * m + r.val) := by
    calc
      _ = ∑' z : ℕ × Fin 3, sharpRankMajorant n (3 * z.1 + z.2.val) :=
        (rankResidueEquiv.symm.tsum_eq (sharpRankMajorant n)).symm
      _ = _ := by rw [hp.tsum_prod]; simp only [tsum_fintype]
  exact heq.trans hgroup.tsum_eq ▸ hs.hasSum

theorem normalised_kernel_le_sharp_rank_weight (a : ℕ) (e : Exponent235)
    (he : 2 ^ a ≤ exponentValue235 e) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e ≤
      1 / (2 * (sharpJumpDenom
        (heightRank235 (exponentValue235 e) - paperJumpIndex a) : ℝ)) := by
  have hh := height_growth_sharp_dyadic a (exponentValue235 e) he
  have hhR : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) *
      (sharpJumpDenom (heightRank235 (exponentValue235 e) - paperJumpIndex a) : ℝ) ≤
      (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) := by exact_mod_cast hh
  have hH : (0 : ℝ) < (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) :=
    threePrimeHeight235_cast_pos _
  have hD : (0 : ℝ) < (sharpJumpDenom
      (heightRank235 (exponentValue235 e) - paperJumpIndex a) : ℝ) := by
    exact_mod_cast sharpJumpDenom_pos _
  unfold exponentKernel235
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hD)).mpr
  apply (mul_le_mul_iff_left₀ hH).mp
  calc
    _ = (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) *
        (sharpJumpDenom (heightRank235 (exponentValue235 e) - paperJumpIndex a) : ℝ) := by
      field_simp [ne_of_gt hH]
      <;> ring
    _ ≤ (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ) := hhR
    _ = _ := by ring
end ErdosProblems.Erdos269.PaperR10

open scoped BigOperators
open PaperR7 PaperR8
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (a : ℕ) (s : Finset Exponent235)
    (hs : ∀ e ∈ s, 2 ^ a ≤ exponentValue235 e) :
    (∑ e ∈ s, (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e) ≤
      (carryMajorantQtilde (paperJumpIndex a) : ℝ) := by
  classical
  let kfun : Exponent235 → ℕ := fun e =>
    heightRank235 (exponentValue235 e) - paperJumpIndex a
  let f : Exponent235 → ℝ := fun e =>
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e
  have hfib : ∀ k ∈ s.image kfun,
      (∑ e ∈ s with kfun e = k, f e) ≤ sharpRankMajorant (paperJumpIndex a) k := by
    intro k _hk
    let t := s.filter (fun e => kfun e = k)
    have ht : ∀ e ∈ t, heightRank235 (exponentValue235 e) = paperJumpIndex a + k := by
      intro e he
      have he' := Finset.mem_filter.mp he
      have hmono := heightRank235_mono (hs e he'.1)
      rw [heightRank235_dyadic] at hmono
      have hek : heightRank235 (exponentValue235 e) - paperJumpIndex a = k := he'.2
      omega
    have hcardN := rank_fibre_card_bound t (paperJumpIndex a + k) ht
    have hcard : (t.card : ℝ) ≤ ((paperJumpIndex a + k + 3 : ℕ) : ℝ) ^ 2 / 9 := by
      have h : (9 : ℝ) * t.card ≤ ((paperJumpIndex a + k + 3 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast hcardN
      linarith
    change (∑ e ∈ t, f e) ≤ _
    calc
      (∑ e ∈ t, f e) ≤ ∑ _e ∈ t, 1 / (2 * (sharpJumpDenom k : ℝ)) := by
        apply Finset.sum_le_sum
        intro e he
        have he' := Finset.mem_filter.mp he
        have hw := normalised_kernel_le_sharp_rank_weight a e (hs e he'.1)
        change f e ≤ 1 / (2 * (sharpJumpDenom (kfun e) : ℝ)) at hw
        rw [he'.2] at hw
        exact hw
      _ = (t.card : ℝ) * (1 / (2 * (sharpJumpDenom k : ℝ))) := by simp
      _ ≤ (((paperJumpIndex a + k + 3 : ℕ) : ℝ) ^ 2 / 9) *
          (1 / (2 * (sharpJumpDenom k : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = sharpRankMajorant (paperJumpIndex a) k := by unfold sharpRankMajorant; ring
  have hsum : (∑ e ∈ s, f e) =
      ∑ k ∈ s.image kfun, ∑ e ∈ s with kfun e = k, f e := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun _e he => Finset.mem_image_of_mem kfun he) f
  change (∑ e ∈ s, f e) ≤ _
  rw [hsum]
  have hfinite := Finset.sum_le_sum hfib
  refine hfinite.trans ?_
  exact sum_le_hasSum (s.image kfun)
    (fun k _ => by unfold sharpRankMajorant; positivity)
    (hasSum_sharpRankMajorant (paperJumpIndex a))
