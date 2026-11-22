-- Prove2me | solution 1 for Erdos390.Full.FiniteProbability.sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:03:13.056059+00:00
-- url     : https://prove2.me/submissions/f80f473a-458b-4c7d-b9cd-bc44d3ddc610

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_FiniteProbability_sum_abs_sigmaMixture_covariance_sub_le

/- Source module: Erdos390.Full.FiniteProbabilityMixturePerturbation -/
section


/-!
# Family-summed perturbations of finite tagged mixtures

The covariance of a tagged mixture contains a between-component term.  Thus
componentwise covariance estimates alone cannot be averaged.  This file
works one level lower: component first moments and mixed moments are compared,
then the exact sigma-mixture expectation formula is used before covariance is
formed.  The resulting theorem keeps an entire finite covariance row under a
single family envelope and includes the between-component contribution.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]









/-- Variant with component covariance-row perturbations as input.  The two
copies of the mean-product loss are deliberate: one converts component
covariances back to mixed moments, and the other is the between-component
covariance of the tagged mixture. -/
theorem sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {AF AH dF dH dCov : ℝ}
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH)
    (hdF : 0 ≤ dF)
    (hFbase : ∀ c, |(mu c).expect (Fmu c)| ≤ AF)
    (hHbase : ∀ c, ∑ i, |(mu c).expect (Hmu c i)| ≤ AH)
    (hFdiff : ∀ c,
      |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ dF)
    (hHdiff : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ dH)
    (hCovdiff : ∀ c, ∑ i,
      |(nu c).covariance (Fnu c) (Hnu c i) -
        (mu c).covariance (Fmu c) (Hmu c i)| ≤ dCov) :
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      dCov + 2 * ((AF + dF) * dH + AH * dF) := by
  have hFnu (c : Cell) : |(nu c).expect (Fnu c)| ≤ AF + dF := by
    calc
      |(nu c).expect (Fnu c)| =
          |((nu c).expect (Fnu c) - (mu c).expect (Fmu c)) +
            (mu c).expect (Fmu c)| := by
        congr 1
        ring
      _ ≤ |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| +
          |(mu c).expect (Fmu c)| := abs_add_le _ _
      _ ≤ dF + AF := add_le_add (hFdiff c) (hFbase c)
      _ = AF + dF := add_comm _ _
  have hprodPoint (c : Cell) (i : I) :
      |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        |(nu c).expect (Fnu c)| *
            |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| +
          |(mu c).expect (Hmu c i)| *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
    rw [show
      (nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i) =
        (nu c).expect (Fnu c) *
            ((nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)) +
          (mu c).expect (Hmu c i) *
            ((nu c).expect (Fnu c) - (mu c).expect (Fmu c)) by ring]
    simpa only [abs_mul] using abs_add_le
      ((nu c).expect (Fnu c) *
        ((nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)))
      ((mu c).expect (Hmu c i) *
        ((nu c).expect (Fnu c) - (mu c).expect (Fmu c)))
  have hprod (c : Cell) :
      ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        (AF + dF) * dH + AH * dF := by
    calc
      ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        ∑ i, (|(nu c).expect (Fnu c)| *
            |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| +
          |(mu c).expect (Hmu c i)| *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)|) :=
        Finset.sum_le_sum fun i hi ↦ hprodPoint c i
      _ = |(nu c).expect (Fnu c)| *
            (∑ i, |(nu c).expect (Hnu c i) -
              (mu c).expect (Hmu c i)|) +
          (∑ i, |(mu c).expect (Hmu c i)|) *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ (AF + dF) * dH + AH * dF := by
        exact add_le_add
          (mul_le_mul (hFnu c) (hHdiff c) (by positivity)
            (add_nonneg hAF hdF))
          (mul_le_mul (hHbase c) (hFdiff c) (by positivity) hAH)
  have hFHdiff (c : Cell) : ∑ i,
      |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
        (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
      dCov + ((AF + dF) * dH + AH * dF) := by
    have hpoint (i : I) :
        |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
            (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
          |(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)| +
          |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| := by
      unfold covariance
      rw [show
        (nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
            (mu c).expect (fun x ↦ Fmu c x * Hmu c i x) =
          ((nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
              (nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            ((mu c).expect (fun x ↦ Fmu c x * Hmu c i x) -
              (mu c).expect (Fmu c) * (mu c).expect (Hmu c i))) +
          ((nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)) by ring]
      exact abs_add_le _ _
    calc
      ∑ i, |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
          (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
        ∑ i, (|(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)| +
          |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)|) :=
        Finset.sum_le_sum fun i hi ↦ hpoint i
      _ = (∑ i, |(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)|) +
          ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| := by
        rw [Finset.sum_add_distrib]
      _ ≤ dCov + ((AF + dF) * dH + AH * dF) :=
        add_le_add (hCovdiff c) (hprod c)
  have hmain := sum_abs_sigmaMixture_covariance_sub_le
    weight mu nu Fmu Fnu Hmu Hnu hAF hAH hdF
      hFbase hHbase hFdiff hHdiff hFHdiff
  calc
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      (dCov + ((AF + dF) * dH + AH * dF)) +
        (AF + dF) * dH + AH * dF := hmain
    _ = dCov + 2 * ((AF + dF) * dH + AH * dF) := by ring



end

end Erdos390.Full.FiniteProbability

end

universe u_1 u_2 u_3 u_4
theorem solution :
∀ {Cell : Type u_1} {I : Type u_2} [inst : Fintype.{u_1} Cell] [inst_1 : Fintype.{u_2} I] {Omega : Cell → Type u_3}
  {Theta : Cell → Type u_4} [inst_2 : (c : Cell) → Fintype.{u_3} (Omega c)]
  [inst_3 : (c : Cell) → Fintype.{u_4} (Theta c)] (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
  (mu : (c : Cell) → Erdos390.Full.FiniteProbability.{u_3} (Omega c))
  (nu : (c : Cell) → Erdos390.Full.FiniteProbability.{u_4} (Theta c)) (Fmu : (c : Cell) → Omega c → Real)
  (Fnu : (c : Cell) → Theta c → Real) (Hmu : (c : Cell) → I → Omega c → Real) (Hnu : (c : Cell) → I → Theta c → Real)
  {AF AH dF dH dCov : Real},
  LE.le.{0} (0 : Real) AF →
    LE.le.{0} (0 : Real) AH →
      LE.le.{0} (0 : Real) dF →
        (∀ (c : Cell), LE.le.{0} (abs.{0} (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Fmu c))) AF) →
          (∀ (c : Cell), LE.le.{0} (∑ i, abs.{0} (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Hmu c i))) AH) →
            (∀ (c : Cell),
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0} (Erdos390.Full.FiniteProbability.expect.{u_4} (nu c) (Fnu c))
                      (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Fmu c))))
                  dF) →
              (∀ (c : Cell),
                  LE.le.{0}
                    (∑ i,
                      abs.{0}
                        (HSub.hSub.{0, 0, 0} (Erdos390.Full.FiniteProbability.expect.{u_4} (nu c) (Hnu c i))
                          (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Hmu c i))))
                    dH) →
                (∀ (c : Cell),
                    LE.le.{0}
                      (∑ i,
                        abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.covariance.{u_4} (nu c) (Fnu c) (Hnu c i))
                            (Erdos390.Full.FiniteProbability.covariance.{u_3} (mu c) (Fmu c) (Hmu c i))))
                      dCov) →
                  LE.le.{0}
                    (∑ i,
                      abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_4}
                            (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, u_4} weight nu)
                            (fun x => Fnu (Sigma.fst.{u_1, u_4} x) (Sigma.snd.{u_1, u_4} x)) fun x =>
                            Hnu (Sigma.fst.{u_1, u_4} x) i (Sigma.snd.{u_1, u_4} x))
                          (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_3}
                            (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, u_3} weight mu)
                            (fun x => Fmu (Sigma.fst.{u_1, u_3} x) (Sigma.snd.{u_1, u_3} x)) fun x =>
                            Hmu (Sigma.fst.{u_1, u_3} x) i (Sigma.snd.{u_1, u_3} x))))
                    (HAdd.hAdd.{0, 0, 0} dCov
                      (HMul.hMul.{0, 0, 0} (2 : Real)
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} AF dF) dH)
                          (HMul.hMul.{0, 0, 0} AH dF)))) := by
  exact @Erdos390.Full.FiniteProbability.sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
