-- Prove2me | solution 1 for Erdos390.Full.FiniteProbability.sum_abs_sigmaMixture_covariance_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:56:54.618451+00:00
-- url     : https://prove2.me/submissions/76a44941-c7d0-4922-94fd-7983062cbed7

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

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

/-- A uniform componentwise expectation perturbation survives an arbitrary
common convex mixture.  The two component sample types may be different. -/
theorem abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    {d : ℝ}
    (hcell : ∀ c, |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ d) :
    |(sigmaMixture weight nu).expect (fun x ↦ Fnu x.1 x.2) -
        (sigmaMixture weight mu).expect (fun x ↦ Fmu x.1 x.2)| ≤ d := by
  rw [sigmaMixture_expect, sigmaMixture_expect]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ c, (weight.mass c * (nu c).expect (Fnu c) -
        weight.mass c * (mu c).expect (Fmu c))| ≤
        ∑ c, |weight.mass c * (nu c).expect (Fnu c) -
          weight.mass c * (mu c).expect (Fmu c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, weight.mass c *
        |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← mul_sub, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
    _ ≤ ∑ c, weight.mass c * d := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- A componentwise `l¹` family of expectation perturbations also survives
mixing without a factor equal to the number of components or row indices. -/
theorem sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {d : ℝ}
    (hcell : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ d) :
    ∑ i, |(sigmaMixture weight nu).expect
          (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).expect
          (fun x ↦ Hmu x.1 i x.2)| ≤ d := by
  have hpoint (i : I) :
      |(sigmaMixture weight nu).expect (fun x ↦ Hnu x.1 i x.2) -
          (sigmaMixture weight mu).expect (fun x ↦ Hmu x.1 i x.2)| ≤
        ∑ c, weight.mass c *
          |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| := by
    rw [sigmaMixture_expect, sigmaMixture_expect,
      ← Finset.sum_sub_distrib]
    calc
      |∑ c, (weight.mass c * (nu c).expect (Hnu c i) -
          weight.mass c * (mu c).expect (Hmu c i))| ≤
          ∑ c, |weight.mass c * (nu c).expect (Hnu c i) -
            weight.mass c * (mu c).expect (Hmu c i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← mul_sub, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
  calc
    ∑ i, |(sigmaMixture weight nu).expect
          (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).expect
          (fun x ↦ Hmu x.1 i x.2)| ≤
        ∑ i, ∑ c, weight.mass c *
          |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = ∑ c, weight.mass c * ∑ i,
        |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ ≤ ∑ c, weight.mass c * d := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- A componentwise `l¹` expectation envelope passes to the tagged mixture.
This is the family analogue of `sigmaMixture_expect_le_common`. -/
theorem sum_abs_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (H : ∀ c, I → Omega c → ℝ)
    {A : ℝ}
    (hcell : ∀ c, ∑ i, |(mu c).expect (H c i)| ≤ A) :
    ∑ i, |(sigmaMixture weight mu).expect
      (fun x ↦ H x.1 i x.2)| ≤ A := by
  have hpoint (i : I) :
      |(sigmaMixture weight mu).expect (fun x ↦ H x.1 i x.2)| ≤
        ∑ c, weight.mass c * |(mu c).expect (H c i)| := by
    rw [sigmaMixture_expect]
    calc
      |∑ c, weight.mass c * (mu c).expect (H c i)| ≤
          ∑ c, |weight.mass c * (mu c).expect (H c i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
  calc
    ∑ i, |(sigmaMixture weight mu).expect
        (fun x ↦ H x.1 i x.2)| ≤
        ∑ i, ∑ c, weight.mass c * |(mu c).expect (H c i)| :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = ∑ c, weight.mass c * ∑ i, |(mu c).expect (H c i)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ ≤ ∑ c, weight.mass c * A := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = A := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- Family-summed covariance stability for two tagged mixtures with the same
component weights.  The hypotheses compare component first moments and mixed
moments, not component covariances, so the conclusion includes the complete
between-component covariance term. -/
theorem sum_abs_sigmaMixture_covariance_sub_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {AF AH dF dH dFH : ℝ}
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH)
    (hdF : 0 ≤ dF)
    (hFbase : ∀ c, |(mu c).expect (Fmu c)| ≤ AF)
    (hHbase : ∀ c, ∑ i, |(mu c).expect (Hmu c i)| ≤ AH)
    (hFdiff : ∀ c,
      |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ dF)
    (hHdiff : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ dH)
    (hFHdiff : ∀ c, ∑ i,
      |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
        (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤ dFH) :
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      dFH + (AF + dF) * dH + AH * dF := by
  let Mu := sigmaMixture weight mu
  let Nu := sigmaMixture weight nu
  let FMu : Sigma Omega → ℝ := fun x ↦ Fmu x.1 x.2
  let FNu : Sigma Theta → ℝ := fun x ↦ Fnu x.1 x.2
  let HMU : I → Sigma Omega → ℝ := fun i x ↦ Hmu x.1 i x.2
  let HNU : I → Sigma Theta → ℝ := fun i x ↦ Hnu x.1 i x.2
  have hFbaseGlobal : |Mu.expect FMu| ≤ AF := by
    rw [sigmaMixture_expect]
    calc
      |∑ c, weight.mass c * (mu c).expect (Fmu c)| ≤
          ∑ c, weight.mass c * |(mu c).expect (Fmu c)| := by
        calc
          _ ≤ ∑ c, |weight.mass c * (mu c).expect (Fmu c)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
      _ ≤ ∑ c, weight.mass c * AF := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_left (hFbase c) (weight.mass_nonneg c)
      _ = AF := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  have hHbaseGlobal : ∑ i, |Mu.expect (HMU i)| ≤ AH := by
    simpa only [Mu, HMU] using
      sum_abs_sigmaMixture_expect_le weight mu Hmu hHbase
  have hFdiffGlobal : |Nu.expect FNu - Mu.expect FMu| ≤ dF := by
    simpa only [Nu, Mu, FNu, FMu] using
      abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
        weight mu nu Fmu Fnu hFdiff
  have hHdiffGlobal : ∑ i, |Nu.expect (HNU i) - Mu.expect (HMU i)| ≤ dH := by
    simpa only [Nu, Mu, HNU, HMU] using
      sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
        weight mu nu Hmu Hnu hHdiff
  have hFHdiffGlobal : ∑ i,
      |Nu.expect (fun x ↦ FNu x * HNU i x) -
        Mu.expect (fun x ↦ FMu x * HMU i x)| ≤ dFH := by
    let PHmu : ∀ c, I → Omega c → ℝ :=
      fun c i x ↦ Fmu c x * Hmu c i x
    let PHnu : ∀ c, I → Theta c → ℝ :=
      fun c i x ↦ Fnu c x * Hnu c i x
    have hraw := sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
      weight mu nu PHmu PHnu hFHdiff
    simpa only [Nu, Mu, FNu, FMu, HNU, HMU, PHmu, PHnu] using hraw
  have hFnu : |Nu.expect FNu| ≤ AF + dF := by
    calc
      |Nu.expect FNu| = |(Nu.expect FNu - Mu.expect FMu) + Mu.expect FMu| := by
        congr 1
        ring
      _ ≤ |Nu.expect FNu - Mu.expect FMu| + |Mu.expect FMu| :=
        abs_add_le _ _
      _ ≤ dF + AF := add_le_add hFdiffGlobal hFbaseGlobal
      _ = AF + dF := add_comm _ _
  have hpoint (i : I) :
      |Nu.covariance FNu (HNU i) - Mu.covariance FMu (HMU i)| ≤
        |Nu.expect (fun x ↦ FNu x * HNU i x) -
            Mu.expect (fun x ↦ FMu x * HMU i x)| +
          |Nu.expect FNu| * |Nu.expect (HNU i) - Mu.expect (HMU i)| +
          |Mu.expect (HMU i)| * |Nu.expect FNu - Mu.expect FMu| := by
    unfold covariance
    have hprod :
        Nu.expect FNu * Nu.expect (HNU i) -
            Mu.expect FMu * Mu.expect (HMU i) =
          Nu.expect FNu * (Nu.expect (HNU i) - Mu.expect (HMU i)) +
            Mu.expect (HMU i) * (Nu.expect FNu - Mu.expect FMu) := by ring
    rw [show
      (Nu.expect (fun x ↦ FNu x * HNU i x) -
          Nu.expect FNu * Nu.expect (HNU i)) -
        (Mu.expect (fun x ↦ FMu x * HMU i x) -
          Mu.expect FMu * Mu.expect (HMU i)) =
        (Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)) -
        (Nu.expect FNu * Nu.expect (HNU i) -
          Mu.expect FMu * Mu.expect (HMU i)) by ring,
      hprod]
    let X := Nu.expect (fun x ↦ FNu x * HNU i x) -
      Mu.expect (fun x ↦ FMu x * HMU i x)
    let Y := Nu.expect FNu * (Nu.expect (HNU i) - Mu.expect (HMU i))
    let Z := Mu.expect (HMU i) * (Nu.expect FNu - Mu.expect FMu)
    change |X - (Y + Z)| ≤ _
    calc
      |X - (Y + Z)| ≤ |X| + |Y + Z| := abs_sub _ _
      _ ≤ |X| + (|Y| + |Z|) :=
        add_le_add (le_refl |X|) (abs_add_le Y Z)
      _ = _ := by
        dsimp only [X, Y, Z]
        simp only [abs_mul]
        ring
  calc
    ∑ i, |Nu.covariance FNu (HNU i) -
        Mu.covariance FMu (HMU i)| ≤
      ∑ i, (|Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)| +
        |Nu.expect FNu| * |Nu.expect (HNU i) - Mu.expect (HMU i)| +
        |Mu.expect (HMU i)| * |Nu.expect FNu - Mu.expect FMu|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)|) +
        |Nu.expect FNu| *
          (∑ i, |Nu.expect (HNU i) - Mu.expect (HMU i)|) +
        (∑ i, |Mu.expect (HMU i)|) *
          |Nu.expect FNu - Mu.expect FMu| := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_mul]
    _ ≤ dFH + (AF + dF) * dH + AH * dF := by
      exact add_le_add
        (add_le_add hFHdiffGlobal
          (mul_le_mul hFnu hHdiffGlobal (by positivity)
            (add_nonneg hAF hdF)))
        (mul_le_mul hHbaseGlobal hFdiffGlobal (by positivity) hAH)





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
  {AF AH dF dH dFH : Real},
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
                            (Erdos390.Full.FiniteProbability.expect.{u_4} (nu c) fun x =>
                              HMul.hMul.{0, 0, 0} (Fnu c x) (Hnu c i x))
                            (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) fun x =>
                              HMul.hMul.{0, 0, 0} (Fmu c x) (Hmu c i x))))
                      dFH) →
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
                    (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} dFH (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} AF dF) dH))
                      (HMul.hMul.{0, 0, 0} AH dF)) := by
  exact @Erdos390.Full.FiniteProbability.sum_abs_sigmaMixture_covariance_sub_le
