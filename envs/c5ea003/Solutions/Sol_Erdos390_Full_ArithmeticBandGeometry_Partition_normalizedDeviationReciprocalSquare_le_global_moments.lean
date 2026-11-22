-- Prove2me | solution 1 for Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare_le_global_moments
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:58:07.163324+00:00
-- url     : https://prove2.me/submissions/1b7197b3-a77a-4b3f-b4a8-078ad7d46063

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PaperNonstepLocalDiagonal -/
section


/-!
# Exact local diagonal estimates for the non-step slow row

The prime-power slow-row ledger leaves the literal cell quantity

`H_i^{-1} sum_{p in cell i} |alpha_i-t_p|/p^2`.

This file bounds that quantity without replacing `t_p` by a step value.
The low-cell estimate retains the two global reciprocal-square moments;
the positive-cell estimate exploits the moving lower endpoint.  Both are
finite identities/inequalities, independent of any tilt box.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PositiveCellTransfer

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)





private theorem sum_bandPrime_inv_sq_eq :
    (∑ p : BandPrime n W, (1 / (p.1 : ℝ)) ^ 2) =
      bandReciprocalSquareSum n W := by
  unfold bandReciprocalSquareSum
  calc
    (∑ p : BandPrime n W, (1 / (p.1 : ℝ)) ^ 2) =
        ∑ p : BandPrime n W, 1 / (p.1 : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact one_div_pow (p.1 : ℝ) 2
    _ = ∑ p ∈ primeBand n W, 1 / (p : ℝ) ^ 2 :=
      (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl)
        (fun p ↦ 1 / (p : ℝ) ^ 2)).symm

private theorem sum_bandPrime_t_inv_sq_eq :
    (∑ p : BandPrime n W,
      tPrime n p.1 * (1 / (p.1 : ℝ)) ^ 2) =
        bandTReciprocalSquareSum n W := by
  unfold bandTReciprocalSquareSum
  exact (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl)
    (fun p ↦ tPrime n p * (1 / (p : ℝ)) ^ 2)).symm

/-- Exact low-cell majorant.  Crucially, neither reciprocal-square moment
is replaced by `1/W` after division by the moving centre. -/
theorem normalizedDeviationReciprocalSquare_le_global_moments
    (hn : 1 < n) (i : Band) :
    P.normalizedDeviationReciprocalSquare i ≤
      (1 / P.mass i) *
        (P.center i * bandReciprocalSquareSum n W +
          bandTReciprocalSquareSum n W) := by
  have hH : 0 < P.mass i := P.data.mass_pos i
  have halpha : 0 < P.center i := by
    change 0 <
      (∑ p ∈ P.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass i
    apply div_pos
    · apply Finset.sum_pos
      · intro p _hp
        apply mul_pos (one_div_pos.mpr (by
          exact_mod_cast (prime_of_mem_primeBand p.2).pos))
        unfold tPrime
        apply div_pos
        · exact Real.log_pos (by
            exact_mod_cast (prime_of_mem_primeBand p.2).one_lt)
        · rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
          exact mul_pos (by norm_num) (Scale.L_pos hn)
      · obtain ⟨p, hp⟩ := P.fiber_nonempty i
        exact ⟨p, by simpa only
          [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp⟩
    · exact hH
  have ht0 (p : BandPrime n W) : 0 ≤ tPrime n p.1 := by
    unfold tPrime
    apply div_nonneg
    · exact Real.log_nonneg
        (by exact_mod_cast (prime_of_mem_primeBand p.2).one_le)
    · rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact (mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn))).le
  have hlocal :
      (∑ p ∈ P.data.fiber i,
          |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2) ≤
        P.center i * bandReciprocalSquareSum n W +
          bandTReciprocalSquareSum n W := by
    calc
      (∑ p ∈ P.data.fiber i,
          |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2) ≤
          ∑ p ∈ P.data.fiber i,
            (P.center i + tPrime n p.1) *
              (1 / (p.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hpBand : P.band p = i :=
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
        unfold deviation
        rw [hpBand]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          |P.center i - tPrime n p.1| ≤
              |P.center i| + |tPrime n p.1| := abs_sub _ _
          _ = P.center i + tPrime n p.1 := by
            rw [abs_of_pos halpha, abs_of_nonneg (ht0 p)]
      _ ≤ ∑ p : BandPrime n W,
            (P.center i + tPrime n p.1) *
              (1 / (p.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro p _hp _hnot
        exact mul_nonneg (add_nonneg halpha.le (ht0 p)) (sq_nonneg _)
      _ = P.center i * bandReciprocalSquareSum n W +
          bandTReciprocalSquareSum n W := by
        rw [← sum_bandPrime_inv_sq_eq (n := n) (W := W),
          ← sum_bandPrime_t_inv_sq_eq (n := n) (W := W)]
        calc
          (∑ p : BandPrime n W,
              (P.center i + tPrime n p.1) *
                (1 / (p.1 : ℝ)) ^ 2) =
              ∑ p : BandPrime n W,
                (P.center i * (1 / (p.1 : ℝ)) ^ 2 +
                  tPrime n p.1 * (1 / (p.1 : ℝ)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro p _hp
            ring
          _ = (∑ p : BandPrime n W,
                P.center i * (1 / (p.1 : ℝ)) ^ 2) +
              ∑ p : BandPrime n W,
                tPrime n p.1 * (1 / (p.1 : ℝ)) ^ 2 :=
            Finset.sum_add_distrib
          _ = P.center i *
                (∑ p : BandPrime n W, (1 / (p.1 : ℝ)) ^ 2) +
              ∑ p : BandPrime n W,
                tPrime n p.1 * (1 / (p.1 : ℝ)) ^ 2 := by
            rw [Finset.mul_sum]
  unfold normalizedDeviationReciprocalSquare
  exact mul_le_mul_of_nonneg_left hlocal (by positivity)



end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

universe u_1
theorem solution :
∀ {n W : Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_1} n W Band),
  LT.lt.{0} (1 : Nat) n →
    ∀ (i : Band),
      LE.le.{0} (Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare.{u_1} P i)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_1} P i))
          (HAdd.hAdd.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_1} P i)
              (Erdos390.Full.PrimeSums.bandReciprocalSquareSum n W))
            (Erdos390.Full.PrimeSums.bandTReciprocalSquareSum n W))) := by
  exact @Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare_le_global_moments
