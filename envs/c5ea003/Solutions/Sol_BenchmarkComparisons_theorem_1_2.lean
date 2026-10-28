-- Prove2me | solution 1 for BenchmarkComparisons.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T06:48:41.79782+00:00
-- url     : https://prove2.me/submissions/43bedfe7-7ad1-4748-bec9-4f2e9776e0f9

import Definitions.Def_BenchmarkRelations
import Theorems.Thm_MeasureEquivalenceMission_lp_iff_le_two
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Pairing

open MeasureTheory Topology Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceInfinity

local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

abbrev RealSequences := ℕ → ℝ
abbrev PrefixSpace (n : ℕ) := PiLp (3 : ℝ≥0∞) (fun _ : Fin n => ℝ)

def finitePrefix (n : ℕ) (x : RealSequences) : PrefixSpace n :=
  WithLp.toLp 3 (fun i => x i)

theorem continuous_finitePrefix (n : ℕ) : Continuous (finitePrefix n) :=
  (PiLp.continuous_toLp 3 (fun _ : Fin n => ℝ)).comp
    (continuous_pi (fun i : Fin n => continuous_apply (i : ℕ)))

def coordinate (x : RealSequences) (i : ℕ × ℕ) : ℝ :=
  dist (finitePrefix i.1 x) (TopologicalSpace.denseSeq (PrefixSpace i.1) i.2) -
    dist (0 : PrefixSpace i.1) (TopologicalSpace.denseSeq (PrefixSpace i.1) i.2)

def infinityCode (x : RealSequences) (n : ℕ) : ℝ := coordinate x (Nat.unpair n)

theorem continuous_infinityCode : Continuous infinityCode := by
  apply continuous_pi
  intro n
  exact ((continuous_finitePrefix (Nat.unpair n).1).dist continuous_const).sub continuous_const

def BoundedDifference (x y : RealSequences) : Prop :=
  ∃ C : ℝ, ∀ n, |x n - y n| ≤ C

theorem norm_finitePrefix_cube (n : ℕ) (x y : RealSequences) :
    ‖finitePrefix n x - finitePrefix n y‖ ^ 3 = ∑ i : Fin n, |x i - y i| ^ (3 : ℕ) := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  have hn : 0 ≤ ∑ i : Fin n, ‖(finitePrefix n x - finitePrefix n y) i‖ ^ (3 : ℝ) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  norm_num only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num
  simp [finitePrefix]

theorem lp3_iff_bounded (x y : RealSequences) :
    Summable (fun n => |x n - y n| ^ (3 : ℝ)) ↔
      BoundedDifference (infinityCode x) (infinityCode y) := by
  simp only [show (3 : ℝ) = (3 : ℕ) from rfl, Real.rpow_natCast]
  constructor
  · intro h
    let S : ℝ := ∑' n, |x n - y n| ^ (3 : ℕ)
    have hS : 0 ≤ S := tsum_nonneg (fun n => pow_nonneg (abs_nonneg _) _)
    refine ⟨S + 1, ?_⟩
    intro k
    let n := (Nat.unpair k).1
    have hsum : ‖finitePrefix n x - finitePrefix n y‖ ^ 3 ≤ S := by
      rw [norm_finitePrefix_cube, Fin.sum_univ_eq_sum_range (fun i => |x i - y i| ^ (3 : ℕ))]
      exact h.sum_le_tsum _ (fun i _ => pow_nonneg (abs_nonneg _) _)
    have hn : ‖finitePrefix n x - finitePrefix n y‖ ≤ S + 1 := by
      by_cases ha : ‖finitePrefix n x - finitePrefix n y‖ ≤ 1
      · linarith
      · have hp := le_self_pow₀ (le_of_lt (lt_of_not_ge ha)) (by decide : (3 : ℕ) ≠ 0)
        linarith
    have hd := abs_dist_sub_le (finitePrefix n x) (finitePrefix n y)
      (TopologicalSpace.denseSeq (PrefixSpace n) (Nat.unpair k).2)
    have he : infinityCode x k - infinityCode y k =
        dist (finitePrefix n x) (TopologicalSpace.denseSeq (PrefixSpace n) (Nat.unpair k).2) -
        dist (finitePrefix n y) (TopologicalSpace.denseSeq (PrefixSpace n) (Nat.unpair k).2) := by
      dsimp [infinityCode, coordinate, n]
      ring
    rw [he]
    exact hd.trans (by simpa only [dist_eq_norm] using hn)
  · rintro ⟨C, hC⟩
    apply summable_of_sum_range_le (fun n => pow_nonneg (abs_nonneg _) _) (c := C ^ 3)
    intro n
    have hdense (k : ℕ) :
        |dist (finitePrefix n x) (TopologicalSpace.denseSeq (PrefixSpace n) k) -
          dist (finitePrefix n y) (TopologicalSpace.denseSeq (PrefixSpace n) k)| ≤ C := by
      have hk := hC (Nat.pair n k)
      dsimp only [infinityCode] at hk
      rw [Nat.unpair_pair] at hk
      dsimp only [coordinate] at hk
      convert hk using 1 <;> congr 1 <;> ring
    have hall : ∀ z : PrefixSpace n, |dist (finitePrefix n x) z - dist (finitePrefix n y) z| ≤ C := by
      intro z
      exact (TopologicalSpace.denseRange_denseSeq (PrefixSpace n)).induction_on z
        (isClosed_le ((continuous_const.dist continuous_id).sub
          (continuous_const.dist continuous_id)).abs continuous_const) hdense
    have hdist : ‖finitePrefix n x - finitePrefix n y‖ ≤ C := by
      simpa only [dist_self, sub_zero, dist_eq_norm, abs_norm]
        using hall (finitePrefix n y)
    rw [← Fin.sum_univ_eq_sum_range (fun i => |x i - y i| ^ (3 : ℕ)), ← norm_finitePrefix_cube]
    exact pow_le_pow_left₀ (norm_nonneg _) hdist 3

theorem exists_continuous_lp3_bounded_reduction :
    ∃ f : RealSequences → RealSequences, Continuous f ∧ Measurable f ∧
      ∀ x y, Summable (fun n => |x n - y n| ^ (3 : ℝ)) ↔ BoundedDifference (f x) (f y) :=
  ⟨infinityCode, continuous_infinityCode, continuous_infinityCode.measurable, lp3_iff_bounded⟩

#print axioms exists_continuous_lp3_bounded_reduction

end MeasureEquivalenceInfinity



open BenchmarkComparisons

theorem solution : ExponentThreshold := by
  have hfinite (p : ℝ) (hp : 1 ≤ p) :
      BorelReduces (LpDifference p) MeasureEquivalent ↔ p ≤ 2 := by
    exact MeasureEquivalenceMission.lp_iff_le_two p hp
  have hinfty : ¬ BorelReduces BoundedDifference MeasureEquivalent := by
    rintro ⟨g, hg, hred⟩
    have hthree : ¬ BorelReduces (LpDifference 3) MeasureEquivalent := by
      intro h
      have := (hfinite 3 (by norm_num)).mp h
      norm_num at this
    apply hthree
    obtain ⟨f, _hc, hf, hiff⟩ :=
      MeasureEquivalenceInfinity.exists_continuous_lp3_bounded_reduction
    exact ⟨g ∘ f, hg.comp hf, fun x y => (hiff x y).trans (hred (f x) (f y))⟩
  intro p hp
  cases p with
  | top => simpa [ExtendedLpDifference] using hinfty
  | coe p =>
    have hp' : 1 ≤ p := by simpa using hp
    change BorelReduces (LpDifference p) MeasureEquivalent ↔
      (p : WithTop ℝ) ≤ ((2 : ℝ) : WithTop ℝ)
    rw [WithTop.coe_le_coe]
    exact hfinite p hp'

#print axioms solution
