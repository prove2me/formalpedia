-- Prove2me | solution 1 for Erdos390.Full.PrimePowerLcmGeometry.sum_highExponents_pair_inv_lcm_eq_diagonalWeight
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:26:15.253583+00:00
-- url     : https://prove2.me/submissions/08136f7d-e9c0-420d-8a1f-f255679eeb1b

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.Full.PrimePowerLcmGeometry -/
section


/-!
# Diagonal prime-power lcm geometry

For the physical-tilt transfer, the diagonal `JJ` orientation contains the
joint divisibility scale `lcm(p^k,p^l)`.  The number of ordered exponent
pairs whose maximum is `r` is exactly `2r-3`.  The identities below keep
that shell multiplicity literal and then invoke the already proved
arithmetic--geometric diagonal mass.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerLcmGeometry

open ArithmeticModel LocalFugacityBounds

noncomputable section

theorem lcm_pow_pow_eq_pow_max (p k l : ℕ) :
    Nat.lcm (p ^ k) (p ^ l) = p ^ max k l := by
  rcases le_total k l with hkl | hlk
  · rw [max_eq_right hkl, Nat.lcm_eq_right_iff_dvd]
    exact pow_dvd_pow p hkl
  · rw [max_eq_left hlk, Nat.lcm_eq_left_iff_dvd]
    exact pow_dvd_pow p hlk

/-- Exact finite shell decomposition of the diagonal reciprocal-lcm sum. -/
theorem sum_highExponents_pair_inv_lcm_eq_diagonalWeight
    (p A : ℕ) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r := by
  induction A with
  | zero => simp [highExponents]
  | succ A ih =>
      cases A with
      | zero => norm_num [highExponents]
      | succ A =>
          let T := Finset.Icc 2 (Nat.succ A)
          let R := Nat.succ (Nat.succ A)
          have hT : highExponents (Nat.succ A) = T := rfl
          have hR : highExponents R = insert R T := by
            apply Finset.ext
            intro x
            simp only [highExponents, T, R, Finset.mem_Icc,
              Finset.mem_insert]
            omega
          have hRT : R ∉ T := by
            dsimp only [R, T]
            simp
          have hkle (k : ℕ) (hk : k ∈ T) : k ≤ R := by
            have hk' := (Finset.mem_Icc.mp hk).2
            dsimp only [R]
            omega
          have hlcmLeft (k : ℕ) (hk : k ∈ T) :
              Nat.lcm (p ^ R) (p ^ k) = p ^ R := by
            rw [lcm_pow_pow_eq_pow_max, max_eq_left (hkle k hk)]
          have hlcmRight (k : ℕ) (hk : k ∈ T) :
              Nat.lcm (p ^ k) (p ^ R) = p ^ R := by
            rw [lcm_pow_pow_eq_pow_max, max_eq_right (hkle k hk)]
          have hcard : T.card = A := by
            dsimp only [T]
            simp
          change
            (∑ k ∈ highExponents R, ∑ l ∈ highExponents R,
                1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
              ∑ r ∈ highExponents R,
                ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r
          rw [hR]
          simp only [Finset.sum_insert hRT]
          rw [show
            (∑ l ∈ T, 1 / (Nat.lcm (p ^ R) (p ^ l) : ℝ)) =
                (T.card : ℝ) * (1 / (p : ℝ) ^ R) by
              calc
                (∑ l ∈ T, 1 / (Nat.lcm (p ^ R) (p ^ l) : ℝ)) =
                    ∑ _l ∈ T, 1 / (p : ℝ) ^ R := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  rw [hlcmLeft l hl]
                  norm_num only [Nat.cast_pow]
                _ = (T.card : ℝ) * (1 / (p : ℝ) ^ R) := by simp]
          rw [show
            (∑ k ∈ T,
                (1 / (Nat.lcm (p ^ k) (p ^ R) : ℝ) +
                  ∑ l ∈ T, 1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ))) =
              (T.card : ℝ) * (1 / (p : ℝ) ^ R) +
                ∑ k ∈ T, ∑ l ∈ T,
                  1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) by
            rw [Finset.sum_add_distrib]
            congr 1
            calc
              (∑ k ∈ T, 1 / (Nat.lcm (p ^ k) (p ^ R) : ℝ)) =
                  ∑ _k ∈ T, 1 / (p : ℝ) ^ R := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hlcmRight k hk]
                norm_num only [Nat.cast_pow]
              _ = (T.card : ℝ) * (1 / (p : ℝ) ^ R) := by simp]
          have ih' :
              (∑ k ∈ T, ∑ l ∈ T,
                  1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
                ∑ r ∈ T,
                  ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r := by
            simpa only [hT] using ih
          rw [ih', hcard]
          have hself : Nat.lcm (p ^ R) (p ^ R) = p ^ R := by simp
          rw [hself]
          norm_num only [Nat.cast_pow]
          have hweight : 2 * R - 3 = 2 * A + 1 := by
            dsimp only [R]
            omega
          rw [hweight]
          push_cast
          ring





end

end Erdos390.Full.PrimePowerLcmGeometry

end

theorem solution :
∀ (p A : Nat),
  Eq.{1}
    (∑ k ∈ Erdos390.Full.ArithmeticModel.highExponents A,
      ∑ l ∈ Erdos390.Full.ArithmeticModel.highExponents A,
        HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(Nat.lcm (HPow.hPow.{0, 0, 0} p k) (HPow.hPow.{0, 0, 0} p l)) : Real))
    (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents A,
      HDiv.hDiv.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)) : Real)
        (HPow.hPow.{0, 0, 0} (↑p : Real) r)) := by
  exact @Erdos390.Full.PrimePowerLcmGeometry.sum_highExponents_pair_inv_lcm_eq_diagonalWeight
