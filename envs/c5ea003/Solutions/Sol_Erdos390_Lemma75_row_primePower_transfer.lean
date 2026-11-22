-- Prove2me | solution 1 for Erdos390.Lemma75.row_primePower_transfer
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:33:05.644954+00:00
-- url     : https://prove2.me/submissions/ebbe51c7-5e62-4c4b-8f52-4f2f2db87dcd

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002

/- Source module: Erdos390.Lemma75 -/
section


/-!
# The finite algebraic core of Lemma 7.5

This file formalizes the part of Lemma 7.5 which is independent of the
marked-friable asymptotics.  The analytic estimates enter only as explicit
hypotheses.  The reciprocal weight `u i` is instantiated in the paper by
`1 / p`, `rowScale i` by `p`, and `invW` by `1 / W`.
-/

open scoped BigOperators

namespace Erdos390.Lemma75



namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]









theorem expect_add (μ : FiniteProbability Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]



theorem expect_const_mul (μ : FiniteProbability Ω) (c : ℝ) (X : Ω → ℝ) :
    μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  simp only [expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring_nf



theorem expect_nonneg (μ : FiniteProbability Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X := by
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (μ.mass_nonneg ω) (hX ω)

theorem expect_mono (μ : FiniteProbability Ω) {X Y : Ω → ℝ}
    (hXY : ∀ ω, X ω ≤ Y ω) : μ.expect X ≤ μ.expect Y := by
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hXY ω) (μ.mass_nonneg ω)



theorem covariance_symm (μ : FiniteProbability Ω) (X Y : Ω → ℝ) :
    μ.covariance X Y = μ.covariance Y X := by
  simp only [covariance]
  congr 1
  · apply congrArg μ.expect
    funext ω
    ring
  · ring

theorem covariance_add_left (μ : FiniteProbability Ω) (X Y Z : Ω → ℝ) :
    μ.covariance (fun ω => X ω + Y ω) Z =
      μ.covariance X Z + μ.covariance Y Z := by
  simp only [covariance, expect_add]
  rw [show (fun ω => (X ω + Y ω) * Z ω) =
      (fun ω => X ω * Z ω + Y ω * Z ω) by
        funext ω
        ring]
  rw [expect_add]
  ring

theorem covariance_add_right (μ : FiniteProbability Ω) (X Y Z : Ω → ℝ) :
    μ.covariance X (fun ω => Y ω + Z ω) =
      μ.covariance X Y + μ.covariance X Z := by
  rw [μ.covariance_symm X (fun ω => Y ω + Z ω)]
  rw [μ.covariance_add_left Y Z X]
  rw [μ.covariance_symm Y X, μ.covariance_symm Z X]

















theorem variance_eq_centered_square (μ : FiniteProbability Ω) (X : Ω → ℝ) :
    μ.variance X = μ.expect (fun ω => (X ω - μ.expect X) ^ 2) := by
  let c := μ.expect X
  rw [show (fun ω => (X ω - μ.expect X) ^ 2) =
      (fun ω => X ω ^ 2 + (-2 * c) * X ω + c ^ 2) by
        funext ω
        dsimp [c]
        ring]
  rw [μ.expect_add, μ.expect_add, μ.expect_const_mul, μ.expect_const]
  simp only [variance, covariance]
  dsimp [c]
  ring_nf

theorem variance_nonneg (μ : FiniteProbability Ω) (X : Ω → ℝ) :
    0 ≤ μ.variance X := by
  rw [μ.variance_eq_centered_square]
  exact μ.expect_nonneg (fun ω => sq_nonneg (X ω - μ.expect X))

end FiniteProbability

section PrimePowerAlgebra

variable {Ω ι κ : Type*} [Fintype Ω]











theorem covariance_full_difference (μ : FiniteProbability Ω)
    (I J : ι → Ω → ℝ) (i j : ι) :
    μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I j ω + J j ω) -
        μ.covariance (I i) (I j) =
      μ.covariance (J i) (I j) +
        μ.covariance (I i) (J j) +
        μ.covariance (J i) (J j) := by
  rw [μ.covariance_add_left, μ.covariance_add_right,
    μ.covariance_add_right]
  ring

theorem abs_covariance_full_difference_le (μ : FiniteProbability Ω)
    (I J : ι → Ω → ℝ) (i j : ι) :
    |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I j ω + J j ω) -
        μ.covariance (I i) (I j)| ≤
      |μ.covariance (J i) (I j)| +
        |μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)| := by
  rw [covariance_full_difference μ I J i j]
  calc
    |μ.covariance (J i) (I j) + μ.covariance (I i) (J j) +
        μ.covariance (J i) (J j)| ≤
      |μ.covariance (J i) (I j) + μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)| := abs_add_le _ _
    _ ≤ |μ.covariance (J i) (I j)| +
        |μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)| := by
      linarith [abs_add_le (μ.covariance (J i) (I j))
        (μ.covariance (I i) (J j))]

/-- The diagonal estimate used in Lemma 7.5.  Its assumptions are the
pointwise identities of a squarefree indicator `I` and its nonnegative
higher-power part `J`. -/
theorem diagonal_difference_le_three_secondMoment
    (μ : FiniteProbability Ω) (I J : Ω → ℝ)
    (hI0 : ∀ ω, 0 ≤ I ω) (hI1 : ∀ ω, I ω ≤ 1)
    (hJ0 : ∀ ω, 0 ≤ J ω) (hJsq : ∀ ω, J ω ≤ J ω ^ 2)
    (hIJ : ∀ ω, I ω * J ω = J ω) :
    |μ.covariance (fun ω => I ω + J ω) (fun ω => I ω + J ω) -
        μ.covariance I I| ≤ 3 * μ.expect (fun ω => J ω ^ 2) := by
  have hEI0 : 0 ≤ μ.expect I := μ.expect_nonneg hI0
  have hEI1 : μ.expect I ≤ 1 := by
    calc
      μ.expect I ≤ μ.expect (fun _ => 1) := μ.expect_mono hI1
      _ = 1 := μ.expect_const 1
  have hEJ0 : 0 ≤ μ.expect J := μ.expect_nonneg hJ0
  have hEJsq0 : 0 ≤ μ.expect (fun ω => J ω ^ 2) :=
    μ.expect_nonneg (fun ω => sq_nonneg (J ω))
  have hEJle : μ.expect J ≤ μ.expect (fun ω => J ω ^ 2) :=
    μ.expect_mono hJsq
  have hcovIJ : μ.covariance I J = μ.expect J * (1 - μ.expect I) := by
    simp only [FiniteProbability.covariance]
    rw [show (fun ω => I ω * J ω) = J by
      funext ω
      exact hIJ ω]
    ring
  have hcovIJ0 : 0 ≤ μ.covariance I J := by
    rw [hcovIJ]
    exact mul_nonneg hEJ0 (by linarith)
  have hcovIJle : μ.covariance I J ≤ μ.expect (fun ω => J ω ^ 2) := by
    rw [hcovIJ]
    have hfactor : 0 ≤ 1 - μ.expect I := by linarith
    have hfactor1 : 1 - μ.expect I ≤ 1 := by linarith
    calc
      μ.expect J * (1 - μ.expect I) ≤ μ.expect J * 1 :=
        mul_le_mul_of_nonneg_left hfactor1 hEJ0
      _ = μ.expect J := by ring
      _ ≤ μ.expect (fun ω => J ω ^ 2) := hEJle
  have hvarJ0 : 0 ≤ μ.variance J := μ.variance_nonneg J
  have hvarJle : μ.variance J ≤ μ.expect (fun ω => J ω ^ 2) := by
    simp only [FiniteProbability.variance, FiniteProbability.covariance]
    rw [show (fun ω => J ω * J ω) = (fun ω => J ω ^ 2) by
      funext ω
      ring]
    exact sub_le_self _ (mul_self_nonneg (μ.expect J))
  have hdiag :
      μ.covariance (fun ω => I ω + J ω) (fun ω => I ω + J ω) -
          μ.covariance I I = 2 * μ.covariance I J + μ.variance J := by
    rw [μ.covariance_add_left, μ.covariance_add_right,
      μ.covariance_add_right, μ.covariance_symm J I]
    simp only [FiniteProbability.variance]
    ring
  rw [hdiag, abs_of_nonneg]
  · linarith
  · nlinarith

end PrimePowerAlgebra

section FiniteContraction

variable {Ω ι κ : Type*} [Fintype Ω]



















set_option maxHeartbeats 800000 in
/-- Pointwise form of the weighted row-norm conclusion of Lemma 7.5.
Taking the supremum over `i ∈ P` gives the paper's row norm.  The three
prime-sum hypotheses are precisely the finite versions of the Mertens
inputs used after the analytic local estimates. -/
theorem row_primePower_transfer [DecidableEq ι]
    (μ : FiniteProbability Ω) (P : Finset ι)
    (I J : ι → Ω → ℝ) (t u rowScale : ι → ℝ)
    (C ε invW HT H1 H2 remRow : ℝ)
    (rJI rIJ rJJ : ι → ι → ℝ) (rD : ι → ℝ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hinv0 : 0 ≤ invW) (hinv1 : invW ≤ 1)
    (ht0 : ∀ i ∈ P, 0 ≤ t i) (ht1 : ∀ i ∈ P, t i ≤ 1)
    (hu0 : ∀ i ∈ P, 0 ≤ u i) (huW : ∀ i ∈ P, u i ≤ invW)
    (hscale0 : ∀ i ∈ P, 0 ≤ rowScale i)
    (hscale : ∀ i ∈ P, rowScale i * u i = 1)
    (hI0 : ∀ i ∈ P, ∀ ω, 0 ≤ I i ω)
    (hI1 : ∀ i ∈ P, ∀ ω, I i ω ≤ 1)
    (hJ0 : ∀ i ∈ P, ∀ ω, 0 ≤ J i ω)
    (hJsq : ∀ i ∈ P, ∀ ω, J i ω ≤ J i ω ^ 2)
    (hIJpoint : ∀ i ∈ P, ∀ ω, I i ω * J i ω = J i ω)
    (hJI : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (I j)| ≤
        C * t i * t j * u i ^ 2 * u j + ε * u i ^ 2 * u j + rJI i j)
    (hIJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (I i) (J j)| ≤
        C * t i * t j * u i * u j ^ 2 + ε * u i * u j ^ 2 + rIJ i j)
    (hJJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (J j)| ≤
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          ε * u i ^ 2 * u j ^ 2 + rJJ i j)
    (hMoment : ∀ i ∈ P,
      μ.expect (fun ω => J i ω ^ 2) ≤ (C + ε) * u i ^ 2 + rD i)
    (hTsum : (∑ j ∈ P, t j * u j) ≤ HT)
    (hUsum : (∑ j ∈ P, u j) ≤ H1)
    (hU2sum : (∑ j ∈ P, u j ^ 2) ≤ H2 * invW)
    (hRowRem : ∀ i ∈ P,
      rowScale i *
        ((∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j)) +
          3 * rD i) ≤ remRow) :
    ∀ i ∈ P,
      rowScale i * ∑ j ∈ P,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)| ≤
      C * (HT + 2 * H2 + 3) * invW +
        ε * (H1 + 2 * H2 + 3) * invW + remRow := by
  intro i hi
  have hui0 := hu0 i hi
  have huiW := huW i hi
  have hti0 := ht0 i hi
  have hti1 := ht1 i hi
  have hs0 := hscale0 i hi
  have hsu := hscale i hi
  have hsu2 : rowScale i * u i ^ 2 = u i := by
    calc
      rowScale i * u i ^ 2 = (rowScale i * u i) * u i := by ring
      _ = u i := by rw [hsu]; ring
  have hTU20 : 0 ≤ ∑ j ∈ P, t j * u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j hj) (sq_nonneg _)
  have hU20 : 0 ≤ ∑ j ∈ P, u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact sq_nonneg _
  have hT0 : 0 ≤ ∑ j ∈ P, t j * u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j hj) (hu0 j hj)
  have hU0 : 0 ≤ ∑ j ∈ P, u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hu0 j hj
  have hTU2 : (∑ j ∈ P, t j * u j ^ 2) ≤ H2 * invW := by
    calc
      (∑ j ∈ P, t j * u j ^ 2) ≤ ∑ j ∈ P, u j ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have huj2 : 0 ≤ u j ^ 2 := sq_nonneg _
        calc
          t j * u j ^ 2 ≤ 1 * u j ^ 2 :=
            mul_le_mul_of_nonneg_right (ht1 j hj) huj2
          _ = u j ^ 2 := by ring
      _ ≤ H2 * invW := hU2sum
  have herase {f : ι → ℝ} (hf : ∀ j ∈ P, 0 ≤ f j) :
      (∑ j ∈ P.erase i, f j) ≤ ∑ j ∈ P, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i P)
      (fun j hjP hjErase => hf j hjP)
  have hTerase : (∑ j ∈ P.erase i, t j * u j) ≤ HT :=
    le_trans (herase (fun j hj => mul_nonneg (ht0 j hj) (hu0 j hj))) hTsum
  have hUerase : (∑ j ∈ P.erase i, u j) ≤ H1 :=
    le_trans (herase hu0) hUsum
  have hU2erase : (∑ j ∈ P.erase i, u j ^ 2) ≤ H2 * invW :=
    le_trans (herase (fun j hj => sq_nonneg _)) hU2sum
  have hTU2erase : (∑ j ∈ P.erase i, t j * u j ^ 2) ≤ H2 * invW :=
    le_trans (herase (fun j hj =>
      mul_nonneg (ht0 j hj) (sq_nonneg _))) hTU2
  have hTerase0 : 0 ≤ ∑ j ∈ P.erase i, t j * u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j (Finset.mem_of_mem_erase hj))
      (hu0 j (Finset.mem_of_mem_erase hj))
  have hTU2erase0 : 0 ≤ ∑ j ∈ P.erase i, t j * u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j (Finset.mem_of_mem_erase hj)) (sq_nonneg _)
  have hUerase0 : 0 ≤ ∑ j ∈ P.erase i, u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hu0 j (Finset.mem_of_mem_erase hj)
  have hU2erase0 : 0 ≤ ∑ j ∈ P.erase i, u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact sq_nonneg _
  have hCJI_sum :
      (∑ j ∈ P.erase i, C * t i * t j * u i ^ 2 * u j) =
        C * t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hCIJ_sum :
      (∑ j ∈ P.erase i, C * t i * t j * u i * u j ^ 2) =
        C * t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hCJJ_sum :
      (∑ j ∈ P.erase i, C * t i * t j * u i ^ 2 * u j ^ 2) =
        C * t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hεJI_sum :
      (∑ j ∈ P.erase i, ε * u i ^ 2 * u j) =
        ε * u i ^ 2 * (∑ j ∈ P.erase i, u j) := by
    rw [Finset.mul_sum]
  have hεIJ_sum :
      (∑ j ∈ P.erase i, ε * u i * u j ^ 2) =
        ε * u i * (∑ j ∈ P.erase i, u j ^ 2) := by
    rw [Finset.mul_sum]
  have hεJJ_sum :
      (∑ j ∈ P.erase i, ε * u i ^ 2 * u j ^ 2) =
        ε * u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2) := by
    rw [Finset.mul_sum]
  have hOff :
      (∑ j ∈ P.erase i,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)|) ≤
      C * (t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j) +
        t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2) +
        t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j ^ 2)) +
      ε * (u i ^ 2 * (∑ j ∈ P.erase i, u j) +
        u i * (∑ j ∈ P.erase i, u j ^ 2) +
        u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) +
      ∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j) := by
    calc
      (∑ j ∈ P.erase i,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)|) ≤
        ∑ j ∈ P.erase i,
          (|μ.covariance (J i) (I j)| + |μ.covariance (I i) (J j)| +
            |μ.covariance (J i) (J j)|) := by
        apply Finset.sum_le_sum
        intro j hj
        exact abs_covariance_full_difference_le μ I J i j
      _ ≤ ∑ j ∈ P.erase i,
          ((C * t i * t j * u i ^ 2 * u j + ε * u i ^ 2 * u j + rJI i j) +
          (C * t i * t j * u i * u j ^ 2 + ε * u i * u j ^ 2 + rIJ i j) +
          (C * t i * t j * u i ^ 2 * u j ^ 2 +
            ε * u i ^ 2 * u j ^ 2 + rJJ i j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact add_le_add (add_le_add (hJI i hi j hj) (hIJ i hi j hj))
          (hJJ i hi j hj)
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [hCJI_sum, hCIJ_sum, hCJJ_sum, hεJI_sum, hεIJ_sum, hεJJ_sum]
        ring
  have hDiag :
      |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I i ω + J i ω) - μ.covariance (I i) (I i)| ≤
        3 * ((C + ε) * u i ^ 2 + rD i) := by
    calc
      |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I i ω + J i ω) - μ.covariance (I i) (I i)| ≤
          3 * μ.expect (fun ω => J i ω ^ 2) :=
        diagonal_difference_le_three_secondMoment μ (I i) (J i)
          (hI0 i hi) (hI1 i hi) (hJ0 i hi) (hJsq i hi)
          (hIJpoint i hi)
      _ ≤ 3 * ((C + ε) * u i ^ 2 + rD i) :=
        mul_le_mul_of_nonneg_left (hMoment i hi) (by norm_num)
  have hrowSplit :
      rowScale i * ∑ j ∈ P,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)| ≤
      rowScale i *
        ((C * (t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j) +
          t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2) +
          t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j ^ 2)) +
        ε * (u i ^ 2 * (∑ j ∈ P.erase i, u j) +
          u i * (∑ j ∈ P.erase i, u j ^ 2) +
          u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) +
        ∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j)) +
        3 * ((C + ε) * u i ^ 2 + rD i)) := by
    apply mul_le_mul_of_nonneg_left _ hs0
    rw [← Finset.sum_erase_add P
      (fun j => |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)|) hi]
    exact add_le_add hOff hDiag
  calc
    rowScale i * ∑ j ∈ P,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)| ≤ _ := hrowSplit
    _ ≤ C * (HT + 2 * H2 + 3) * invW +
        ε * (H1 + 2 * H2 + 3) * invW + remRow := by
      have hCT1 :
          rowScale i * (t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j)) ≤
            invW * HT := by
        have htiuW : t i * u i ≤ invW := by
          calc
            t i * u i ≤ 1 * u i := mul_le_mul_of_nonneg_right hti1 hui0
            _ = u i := one_mul _
            _ ≤ invW := huiW
        calc
          rowScale i * (t i * u i ^ 2 *
              (∑ j ∈ P.erase i, t j * u j)) =
              (t i * u i) * (∑ j ∈ P.erase i, t j * u j) := by
                calc
                  rowScale i * (t i * u i ^ 2 *
                      (∑ j ∈ P.erase i, t j * u j)) =
                      t i * (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, t j * u j) := by ring
                  _ = (t i * u i) * (∑ j ∈ P.erase i, t j * u j) := by
                    rw [hsu2]
          _ ≤ invW * HT :=
            mul_le_mul htiuW hTerase hTerase0 hinv0
      have hCT2 :
          rowScale i * (t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2)) ≤
            H2 * invW := by
        calc
          rowScale i * (t i * u i *
              (∑ j ∈ P.erase i, t j * u j ^ 2)) =
              t i * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
                calc
                  rowScale i * (t i * u i *
                      (∑ j ∈ P.erase i, t j * u j ^ 2)) =
                      t i * (rowScale i * u i) *
                        (∑ j ∈ P.erase i, t j * u j ^ 2) := by ring
                  _ = t i * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
                    rw [hsu]
                    ring
          _ ≤ 1 * (∑ j ∈ P.erase i, t j * u j ^ 2) :=
            mul_le_mul_of_nonneg_right hti1 hTU2erase0
          _ = ∑ j ∈ P.erase i, t j * u j ^ 2 := one_mul _
          _ ≤ H2 * invW := hTU2erase
      have hCT3 :
          rowScale i * (t i * u i ^ 2 *
            (∑ j ∈ P.erase i, t j * u j ^ 2)) ≤ H2 * invW := by
        have htiu : t i * u i ≤ 1 := by
          calc
            t i * u i ≤ 1 * u i := mul_le_mul_of_nonneg_right hti1 hui0
            _ = u i := by ring
            _ ≤ invW := huiW
            _ ≤ 1 := hinv1
        calc
          rowScale i * (t i * u i ^ 2 *
              (∑ j ∈ P.erase i, t j * u j ^ 2)) =
              (t i * u i) * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
                calc
                  rowScale i * (t i * u i ^ 2 *
                      (∑ j ∈ P.erase i, t j * u j ^ 2)) =
                      t i * (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, t j * u j ^ 2) := by ring
                  _ = (t i * u i) *
                      (∑ j ∈ P.erase i, t j * u j ^ 2) := by rw [hsu2]
          _ ≤ 1 * (∑ j ∈ P.erase i, t j * u j ^ 2) :=
            mul_le_mul_of_nonneg_right htiu hTU2erase0
          _ = ∑ j ∈ P.erase i, t j * u j ^ 2 := one_mul _
          _ ≤ H2 * invW := hTU2erase
      have hEU1 :
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j)) ≤ invW * H1 := by
        calc
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j)) =
              u i * (∑ j ∈ P.erase i, u j) := by
                calc
                  rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j)) =
                      (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, u j) := by ring
                  _ = u i * (∑ j ∈ P.erase i, u j) := by rw [hsu2]
          _ ≤ invW * H1 := mul_le_mul huiW hUerase hUerase0 hinv0
      have hEU2 :
          rowScale i * (u i * (∑ j ∈ P.erase i, u j ^ 2)) ≤ H2 * invW := by
        rw [show rowScale i * (u i * (∑ j ∈ P.erase i, u j ^ 2)) =
          (∑ j ∈ P.erase i, u j ^ 2) by rw [show rowScale i *
            (u i * (∑ j ∈ P.erase i, u j ^ 2)) =
              (rowScale i * u i) * (∑ j ∈ P.erase i, u j ^ 2) by ring,
            hsu, one_mul]]
        exact hU2erase
      have hEU3 :
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) ≤
            H2 * invW := by
        have hui1 : u i ≤ 1 := le_trans huiW hinv1
        calc
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) =
              u i * (∑ j ∈ P.erase i, u j ^ 2) := by
                calc
                  rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) =
                      (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, u j ^ 2) := by ring
                  _ = u i * (∑ j ∈ P.erase i, u j ^ 2) := by rw [hsu2]
          _ ≤ 1 * (∑ j ∈ P.erase i, u j ^ 2) :=
            mul_le_mul_of_nonneg_right hui1 hU2erase0
          _ = ∑ j ∈ P.erase i, u j ^ 2 := one_mul _
          _ ≤ H2 * invW := hU2erase
      have hDiagMain : rowScale i * (3 * (C + ε) * u i ^ 2) ≤
          3 * (C + ε) * invW := by
        rw [show rowScale i * (3 * (C + ε) * u i ^ 2) =
          3 * (C + ε) * (rowScale i * u i ^ 2) by ring, hsu2]
        exact mul_le_mul_of_nonneg_left huiW
          (mul_nonneg (by norm_num) (add_nonneg hC hε))
      have hR := hRowRem i hi
      nlinarith

end FiniteContraction

end Erdos390.Lemma75

end

universe u_1 u_2
theorem solution :
∀ {Ω : Type u_1} {ι : Type u_2} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_2 + 1} ι]
  (μ : Erdos390.Lemma75.FiniteProbability.{u_1} Ω) (P : Finset.{u_2} ι) (I J : ι → Ω → Real) (t u rowScale : ι → Real)
  (C ε invW HT H1 H2 remRow : Real) (rJI rIJ rJJ : ι → ι → Real) (rD : ι → Real),
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) ε →
      LE.le.{0} (0 : Real) invW →
        LE.le.{0} invW (1 : Real) →
          (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (0 : Real) (t i)) →
            (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (t i) (1 : Real)) →
              (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (0 : Real) (u i)) →
                (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (u i) invW) →
                  (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (0 : Real) (rowScale i)) →
                    (∀ (i : ι),
                        Membership.mem.{u_2, u_2} P i → Eq.{1} (HMul.hMul.{0, 0, 0} (rowScale i) (u i)) (1 : Real)) →
                      (∀ (i : ι), Membership.mem.{u_2, u_2} P i → ∀ (ω : Ω), LE.le.{0} (0 : Real) (I i ω)) →
                        (∀ (i : ι), Membership.mem.{u_2, u_2} P i → ∀ (ω : Ω), LE.le.{0} (I i ω) (1 : Real)) →
                          (∀ (i : ι), Membership.mem.{u_2, u_2} P i → ∀ (ω : Ω), LE.le.{0} (0 : Real) (J i ω)) →
                            (∀ (i : ι),
                                Membership.mem.{u_2, u_2} P i →
                                  ∀ (ω : Ω), LE.le.{0} (J i ω) (HPow.hPow.{0, 0, 0} (J i ω) (2 : Nat))) →
                              (∀ (i : ι),
                                  Membership.mem.{u_2, u_2} P i →
                                    ∀ (ω : Ω), Eq.{1} (HMul.hMul.{0, 0, 0} (I i ω) (J i ω)) (J i ω)) →
                                (∀ (i : ι),
                                    Membership.mem.{u_2, u_2} P i →
                                      ∀ (j : ι),
                                        Membership.mem.{u_2, u_2} (Finset.erase.{u_2} P i) j →
                                          LE.le.{0}
                                            (abs.{0}
                                              (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ (J i) (I j)))
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (t i)) (t j))
                                                    (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                  (u j))
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} ε (HPow.hPow.{0, 0, 0} (u i) (2 : Nat))) (u j)))
                                              (rJI i j))) →
                                  (∀ (i : ι),
                                      Membership.mem.{u_2, u_2} P i →
                                        ∀ (j : ι),
                                          Membership.mem.{u_2, u_2} (Finset.erase.{u_2} P i) j →
                                            LE.le.{0}
                                              (abs.{0}
                                                (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ (I i) (J j)))
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (t i)) (t j)) (u i))
                                                    (HPow.hPow.{0, 0, 0} (u j) (2 : Nat)))
                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} ε (u i))
                                                    (HPow.hPow.{0, 0, 0} (u j) (2 : Nat))))
                                                (rIJ i j))) →
                                    (∀ (i : ι),
                                        Membership.mem.{u_2, u_2} P i →
                                          ∀ (j : ι),
                                            Membership.mem.{u_2, u_2} (Finset.erase.{u_2} P i) j →
                                              LE.le.{0}
                                                (abs.{0}
                                                  (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ (J i) (J j)))
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (t i)) (t j))
                                                        (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                      (HPow.hPow.{0, 0, 0} (u j) (2 : Nat)))
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0} ε (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                      (HPow.hPow.{0, 0, 0} (u j) (2 : Nat))))
                                                  (rJJ i j))) →
                                      (∀ (i : ι),
                                          Membership.mem.{u_2, u_2} P i →
                                            LE.le.{0}
                                              (Erdos390.Lemma75.FiniteProbability.expect.{u_1} μ fun ω =>
                                                HPow.hPow.{0, 0, 0} (J i ω) (2 : Nat))
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} C ε)
                                                  (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                (rD i))) →
                                        LE.le.{0} (∑ j ∈ P, HMul.hMul.{0, 0, 0} (t j) (u j)) HT →
                                          LE.le.{0} (∑ j ∈ P, u j) H1 →
                                            LE.le.{0} (∑ j ∈ P, HPow.hPow.{0, 0, 0} (u j) (2 : Nat))
                                                (HMul.hMul.{0, 0, 0} H2 invW) →
                                              (∀ (i : ι),
                                                  Membership.mem.{u_2, u_2} P i →
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0} (rowScale i)
                                                        (HAdd.hAdd.{0, 0, 0}
                                                          (∑ j ∈ Finset.erase.{u_2} P i,
                                                            HAdd.hAdd.{0, 0, 0}
                                                              (HAdd.hAdd.{0, 0, 0} (rJI i j) (rIJ i j)) (rJJ i j))
                                                          (HMul.hMul.{0, 0, 0} (3 : Real) (rD i))))
                                                      remRow) →
                                                ∀ (i : ι),
                                                  Membership.mem.{u_2, u_2} P i →
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0} (rowScale i)
                                                        (∑ j ∈ P,
                                                          abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ
                                                                (fun ω => HAdd.hAdd.{0, 0, 0} (I i ω) (J i ω)) fun ω =>
                                                                HAdd.hAdd.{0, 0, 0} (I j ω) (J j ω))
                                                              (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ
                                                                (I i) (I j)))))
                                                      (HAdd.hAdd.{0, 0, 0}
                                                        (HAdd.hAdd.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0} C
                                                              (HAdd.hAdd.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} HT
                                                                  (HMul.hMul.{0, 0, 0} (2 : Real) H2))
                                                                (3 : Real)))
                                                            invW)
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0} ε
                                                              (HAdd.hAdd.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} H1
                                                                  (HMul.hMul.{0, 0, 0} (2 : Real) H2))
                                                                (3 : Real)))
                                                            invW))
                                                        remRow) := by
  exact @Erdos390.Lemma75.row_primePower_transfer
