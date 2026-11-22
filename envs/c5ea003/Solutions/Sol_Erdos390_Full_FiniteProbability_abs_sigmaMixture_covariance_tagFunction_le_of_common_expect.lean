-- Prove2me | solution 1 for Erdos390.Full.FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:54:55.958737+00:00
-- url     : https://prove2.me/submissions/783db1a3-b2d6-446a-9bf2-2240621d0c0e

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.FiniteProbabilityCellConstantCovariance -/
section


/-!
# Covariance with a component-constant mark

If a statistic has the same componentwise expectation profile up to an
error, then its covariance with any bounded function of the component tag is
of that same error size.  This elementary mixture identity is the exact
between-cell estimate needed for the fixed head coordinates in Lemma 8.6.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]

/-- A common component expectation profile makes the covariance with a
bounded tag function small.  The conclusion includes the between-component
covariance; it is not an average of within-component covariances. -/
theorem abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) (H : Cell → ℝ)
    (main error K : ℝ)
    (herror : 0 ≤ error) (hK : 0 ≤ K)
    (hH : ∀ c, |H c| ≤ K)
    (hcell : ∀ c,
      |(mu c).expect (fun x ↦ F ⟨c, x⟩) - main| ≤ error) :
    |(sigmaMixture weight mu).covariance F (fun x ↦ H x.1)| ≤
      2 * K * error := by
  let E : Cell → ℝ := fun c ↦ (mu c).expect (fun x ↦ F ⟨c, x⟩)
  let d : Cell → ℝ := fun c ↦ E c - main
  have hprod (c : Cell) :
      (mu c).expect (fun x ↦ F ⟨c, x⟩ * H c) = H c * E c := by
    have hfun : (fun x ↦ F ⟨c, x⟩ * H c) =
        fun x ↦ H c * F ⟨c, x⟩ := by
      funext x
      ring
    rw [hfun, (mu c).expect_smul]
  have htag (c : Cell) : (mu c).expect (fun _ ↦ H c) = H c := by
    unfold expect
    rw [← Finset.sum_mul, (mu c).mass_sum, one_mul]
  have hcov :
      (sigmaMixture weight mu).covariance F (fun x ↦ H x.1) =
        (∑ c, weight.mass c * H c * d c) -
          (∑ c, weight.mass c * d c) *
            (∑ c, weight.mass c * H c) := by
    unfold covariance
    rw [sigmaMixture_expect, sigmaMixture_expect,
      sigmaMixture_expect]
    simp_rw [hprod, htag]
    change (∑ c, weight.mass c * (H c * E c)) -
        (∑ c, weight.mass c * E c) *
          (∑ c, weight.mass c * H c) = _
    have hE (c : Cell) : E c = main + d c := by
      dsimp only [d]
      ring
    simp_rw [hE]
    have hmassMain :
        ∑ c, weight.mass c * main = main := by
      rw [← Finset.sum_mul, weight.mass_sum, one_mul]
    rw [show (∑ c, weight.mass c * (main + d c)) =
        main + ∑ c, weight.mass c * d c by
      calc
        _ = (∑ c, weight.mass c * main) +
            ∑ c, weight.mass c * d c := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro c hc
          ring
        _ = _ := by rw [hmassMain]]
    have hfirst :
        (∑ c, weight.mass c * (H c * (main + d c))) =
          main * (∑ c, weight.mass c * H c) +
            ∑ c, weight.mass c * H c * d c := by
      calc
        _ = ∑ c,
            (main * (weight.mass c * H c) +
              weight.mass c * H c * d c) := by
          apply Finset.sum_congr rfl
          intro c hc
          ring
        _ = (∑ c, main * (weight.mass c * H c)) +
            ∑ c, weight.mass c * H c * d c :=
          Finset.sum_add_distrib
        _ = _ := by rw [← Finset.mul_sum]
    rw [hfirst]
    ring
  have hA :
      |(∑ c, weight.mass c * H c * d c)| ≤ K * error := by
    calc
      |(∑ c, weight.mass c * H c * d c)| ≤
          ∑ c, |weight.mass c * H c * d c| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, weight.mass c * K * error := by
        apply Finset.sum_le_sum
        intro c hc
        rw [abs_mul, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
        have hd : |d c| ≤ error := by
          exact hcell c
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hH c) (weight.mass_nonneg c))
          hd (abs_nonneg _) (mul_nonneg (weight.mass_nonneg c) hK)
      _ = K * error := by
        calc
          _ = (∑ c, weight.mass c) * K * error := by
            rw [Finset.sum_mul, Finset.sum_mul]
          _ = K * error := by rw [weight.mass_sum, one_mul]
  have hB : |(∑ c, weight.mass c * d c)| ≤ error := by
    calc
      |(∑ c, weight.mass c * d c)| ≤
          ∑ c, |weight.mass c * d c| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, weight.mass c * error := by
        apply Finset.sum_le_sum
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
        exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
      _ = error := by
        rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  have hC : |(∑ c, weight.mass c * H c)| ≤ K := by
    calc
      |(∑ c, weight.mass c * H c)| ≤
          ∑ c, |weight.mass c * H c| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, weight.mass c * K := by
        apply Finset.sum_le_sum
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
        exact mul_le_mul_of_nonneg_left (hH c) (weight.mass_nonneg c)
      _ = K := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  rw [hcov]
  calc
    |(∑ c, weight.mass c * H c * d c) -
        (∑ c, weight.mass c * d c) *
          (∑ c, weight.mass c * H c)| ≤
      |(∑ c, weight.mass c * H c * d c)| +
        |(∑ c, weight.mass c * d c) *
          (∑ c, weight.mass c * H c)| := abs_sub _ _
    _ ≤ K * error + error * K := by
      gcongr
      rw [abs_mul]
      exact mul_le_mul hB hC (abs_nonneg _) herror
    _ = 2 * K * error := by ring

end

end FiniteProbability
end Erdos390.Full

end

universe u_1 u_2
theorem solution :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
  (mu : (c : Cell) → Erdos390.Full.FiniteProbability.{u_2} (Omega c)) (F : Sigma.{u_1, u_2} Omega → Real)
  (H : Cell → Real) (main error K : Real),
  LE.le.{0} (0 : Real) error →
    LE.le.{0} (0 : Real) K →
      (∀ (c : Cell), LE.le.{0} (abs.{0} (H c)) K) →
        (∀ (c : Cell),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.expect.{u_2} (mu c) fun x => F (Sigma.mk.{u_1, u_2} c x)) main))
              error) →
          LE.le.{0}
            (abs.{0}
              (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_2}
                (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, u_2} weight mu) F fun x =>
                H (Sigma.fst.{u_1, u_2} x)))
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) K) error) := by
  exact @Erdos390.Full.FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
