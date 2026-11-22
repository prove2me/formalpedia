-- Prove2me | solution 1 for Erdos390.Full.FiniteSignedQuadraticEntryTransfer.abs_matrixQuadratic_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:03:49.190048+00:00
-- url     : https://prove2.me/submissions/706e5bb3-c22e-4b0d-8858-0de8d2fa1bd4

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.FiniteSignedQuadraticEntryTransfer -/
section


/-!
# Entrywise transfer for finite signed quadratic forms

This is the exact finite summation used to pass from the signed Dickman
reference matrix to the genuine squarefree covariance matrix.  In
particular, the proof keeps the off-diagonal product-reciprocal error and
the two diagonal errors separate; it never replaces a sum of absolute
values by the absolute value of a sum.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteSignedQuadraticEntryTransfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









/-- Product-weight off-diagonal errors and first- and second-weight diagonal
errors aggregate with exactly the corresponding `L¹` and `L²` ledgers. -/
theorem abs_matrixQuadratic_sub_le
    (A B : ι → ι → ℝ) (weight c : ι → ℝ)
    {epsilonOff epsilonDiag epsilonSecond : ℝ}
    (hentry : ∀ i j,
      |A i j - B i j| ≤
        epsilonOff * weight i * weight j +
          if i = j then
            epsilonDiag * weight i + epsilonSecond * weight i ^ 2
          else 0) :
    |matrixQuadratic A c - matrixQuadratic B c| ≤
      epsilonOff * weightedL1 weight c ^ 2 +
        epsilonDiag * weightedL2Sq weight c +
        epsilonSecond * weightedL2SqSecond weight c := by
  classical
  have hsum :
      matrixQuadratic A c - matrixQuadratic B c =
        ∑ i, ∑ j, c i * c j * (A i j - B i j) := by
    unfold matrixQuadratic
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  calc
    |∑ i, ∑ j, c i * c j * (A i j - B i j)| ≤
        ∑ i, |∑ j, c i * c j * (A i j - B i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |c i * c j * (A i j - B i j)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |c i| * |c j| * |A i j - B i j| := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_mul]
    _ ≤ ∑ i, ∑ j, |c i| * |c j| *
        (epsilonOff * weight i * weight j +
          if i = j then
            epsilonDiag * weight i + epsilonSecond * weight i ^ 2
          else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hentry i j)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = epsilonOff * weightedL1 weight c ^ 2 +
        epsilonDiag * weightedL2Sq weight c +
        epsilonSecond * weightedL2SqSecond weight c := by
      unfold weightedL1 weightedL2Sq weightedL2SqSecond
      simp_rw [mul_add]
      rw [show (∑ i, ∑ j,
          (|c i| * |c j| * (epsilonOff * weight i * weight j) +
            |c i| * |c j| *
              (if i = j then
                epsilonDiag * weight i + epsilonSecond * weight i ^ 2
              else 0))) =
          (∑ i, ∑ j, |c i| * |c j| *
            (epsilonOff * weight i * weight j)) +
          ∑ i, ∑ j, |c i| * |c j| *
            (if i = j then
              epsilonDiag * weight i + epsilonSecond * weight i ^ 2
            else 0) by
        simp only [Finset.sum_add_distrib]]
      have hoff :
          (∑ i, ∑ j, |c i| * |c j| *
              (epsilonOff * weight i * weight j)) =
            epsilonOff * (∑ i, weight i * |c i|) ^ 2 := by
        let S : ℝ := ∑ i, weight i * |c i|
        change (∑ i, ∑ j, |c i| * |c j| *
            (epsilonOff * weight i * weight j)) = epsilonOff * S ^ 2
        calc
          (∑ i, ∑ j, |c i| * |c j| *
              (epsilonOff * weight i * weight j)) =
              ∑ i, (epsilonOff * (weight i * |c i|)) * S := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp only [S]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = epsilonOff * S * S := by
            rw [← Finset.sum_mul]
            congr 1
            rw [Finset.mul_sum]
          _ = epsilonOff * S ^ 2 := by ring
      have hdiag :
          (∑ i, ∑ j, |c i| * |c j| *
              (if i = j then
                epsilonDiag * weight i + epsilonSecond * weight i ^ 2
              else 0)) =
            epsilonDiag * (∑ i, weight i * c i ^ 2) +
              epsilonSecond * (∑ i, weight i ^ 2 * c i ^ 2) := by
        calc
          _ = ∑ i, |c i| * |c i| *
              (epsilonDiag * weight i + epsilonSecond * weight i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_eq_single i]
            · simp
            · intro j hj hji
              simp [Ne.symm hji]
            · exact fun hi' ↦ (hi' (Finset.mem_univ i)).elim
          _ = ∑ i,
              (epsilonDiag * (weight i * c i ^ 2) +
                epsilonSecond * (weight i ^ 2 * c i ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hc : |c i| * |c i| = c i ^ 2 := by
              rw [← pow_two, sq_abs]
            rw [hc]
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [hoff, hdiag]
      ring

end Erdos390.Full.FiniteSignedQuadraticEntryTransfer

end

universe u_1
theorem solution :
∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι] (A B : ι → ι → Real) (weight c : ι → Real)
  {epsilonOff epsilonDiag epsilonSecond : Real},
  (∀ (i j : ι),
      LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (A i j) (B i j)))
        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff (weight i)) (weight j))
          (ite.{1} (Eq.{u_1 + 1} i j)
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (weight i))
              (HMul.hMul.{0, 0, 0} epsilonSecond (HPow.hPow.{0, 0, 0} (weight i) (2 : Nat))))
            (0 : Real)))) →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0} (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.matrixQuadratic.{u_1} A c)
          (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.matrixQuadratic.{u_1} B c)))
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} epsilonOff
            (HPow.hPow.{0, 0, 0} (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.weightedL1.{u_1} weight c)
              (2 : Nat)))
          (HMul.hMul.{0, 0, 0} epsilonDiag
            (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.weightedL2Sq.{u_1} weight c)))
        (HMul.hMul.{0, 0, 0} epsilonSecond
          (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.weightedL2SqSecond.{u_1} weight c))) := by
  exact @Erdos390.Full.FiniteSignedQuadraticEntryTransfer.abs_matrixQuadratic_sub_le
