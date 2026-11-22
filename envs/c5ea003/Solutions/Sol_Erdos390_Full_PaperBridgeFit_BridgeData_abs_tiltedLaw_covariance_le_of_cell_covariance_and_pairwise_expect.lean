-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:13:12.953297+00:00
-- url     : https://prove2.me/submissions/2992dc87-6701-45e6-9da3-ede498d1f751

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_FiniteProbability_abs_sigmaMixture_covariance_tagFunction_le_of_common_expect

/- Source module: Erdos390.Full.FiniteProbabilityMixtureTilt -/
section


/-!
# Exponential tilts of finite tagged mixtures

A global exponential tilt of a finite mixture is not obtained by retaining
the old cell weights.  The exact new weights contain the cell partition
functions.  This file proves that identity before any covariance is formed,
so common-profile estimates can safely be averaged across cells.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]









/-- Pointwise exact factorization of the globally tilted density into the
new cell weight and the componentwise tilted density. -/
theorem exponentialTilt_sigmaMixture_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (x : Sigma Omega) :
    ((sigmaMixture weight mu).exponentialTilt S).mass x =
      (sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c))).mass x := by
  rcases x with ⟨c, x⟩
  let Zc := (mu c).expPartition (sigmaCellScore S c)
  let Z := (sigmaMixture weight mu).expPartition S
  have hcellZ : Zc ≠ 0 :=
    ne_of_gt ((mu c).expPartition_pos (sigmaCellScore S c))
  have hglobalZ : Z ≠ 0 :=
    ne_of_gt ((sigmaMixture weight mu).expPartition_pos S)
  change weight.mass c * (mu c).mass x * Real.exp (S ⟨c, x⟩) / Z =
    (weight.mass c * Zc / Z) *
      ((mu c).mass x * Real.exp (S ⟨c, x⟩) / Zc)
  field_simp [hcellZ, hglobalZ]

private theorem finiteProbability_ext
    {Alpha : Type*} [Fintype Alpha]
    {mu nu : FiniteProbability Alpha} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
    cases nu with
    | mk massNu nonnegNu sumNu =>
      dsimp only at h
      subst massNu
      rfl

/-- Equality of the two finite probability laws, not merely equality of
their expectations. -/
theorem exponentialTilt_sigmaMixture
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).exponentialTilt S =
      sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c)) := by
  apply finiteProbability_ext
  funext x
  exact exponentialTilt_sigmaMixture_mass weight mu S x





end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeCellTiltDecomposition -/
section


/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



























/-- The actual bridge law, with the global cell partition functions handled
correctly, is a tagged mixture of the componentwise tilted guard-deleted
cell laws. -/
theorem tiltedLaw_eq_tiltedSigmaMixture [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦ (B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline]
  exact exponentialTilt_sigmaMixture _ _ _



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNuisancePrimeLogRows -/
section


/-!
# Exact logarithmic decomposition of the nuisance rows

The physical nuisance coordinate is not an unrelated marked statistic.  The
finite factorization identity in `BridgeData.HasPrimeLogCompatibility`
expresses the medium-prime logarithmic score as a nonzero multiple of the
physical logarithm plus a function of the fixed head tag.  This file solves
that identity for the physical score and does so inside an arbitrary nuisance
linear functional.

The resulting covariance-row identity is exact at finite `n`.  It is the
algebraic attachment used in Lemma 8.6 before applying the analytic estimates
for the prime-log null row and for cell-constant head rows.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























/-- Exact total-covariance estimate for the actual globally tilted bridge
law.  A bound for every within-cell covariance is combined with pairwise
agreement of the first statistic's component means.  The second statistic
may vary inside a cell; only a pointwise bound is required.  Thus the
between-cell term is accounted for explicitly rather than silently replacing
the global covariance by an average of component covariances. -/
theorem abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
    [Nonempty Head]
    (xi : B.ParamSpace)
    (F G : B.sampleData.Sample → ℝ)
    {covError meanError K : ℝ}
    (hmeanError : 0 ≤ meanError)
    (hK : 0 ≤ K)
    (hcellCov : ∀ c : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).covariance
          (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| ≤ covError)
    (hpair : ∀ c c' : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ F ⟨c', x⟩)| ≤ meanError)
    (hG : ∀ m, |G m| ≤ K) :
    |(B.tiltedLaw xi).covariance F G| ≤
      covError + 2 * K * meanError := by
  let weight := FiniteProbability.tiltedSigmaWeight
    B.baselineCellProbability B.guardedCellProbability
      (B.scaledBridgeScore xi)
  let mu : ∀ c : Cell Head, FiniteProbability (B.sampleData.SampleAt c) :=
    fun c ↦ (B.guardedCellProbability c).exponentialTilt
      (FiniteProbability.sigmaCellScore (B.scaledBridgeScore xi) c)
  let H : Cell Head → ℝ := fun c ↦
    (mu c).expect (fun x ↦ G ⟨c, x⟩)
  let mix : FiniteProbability B.sampleData.Sample :=
    FiniteProbability.sigmaMixture weight mu
  let c₀ : Cell Head := (Classical.choice inferInstance, PhysicalSign.minus)
  let main : ℝ := (mu c₀).expect (fun x ↦ F ⟨c₀, x⟩)
  have hH : ∀ c, |H c| ≤ K := by
    intro c
    unfold H FiniteProbability.expect
    calc
      |∑ x, (mu c).mass x * G ⟨c, x⟩| ≤
          ∑ x, |(mu c).mass x * G ⟨c, x⟩| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, (mu c).mass x * |G ⟨c, x⟩| := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_mul, abs_of_nonneg ((mu c).mass_nonneg x)]
      _ ≤ ∑ x, (mu c).mass x * K := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hG ⟨c, x⟩) ((mu c).mass_nonneg x)
      _ = K := by rw [← Finset.sum_mul, (mu c).mass_sum, one_mul]
  have hcommon : ∀ c,
      |(mu c).expect (fun x ↦ F ⟨c, x⟩) - main| ≤ meanError := by
    intro c
    exact hpair c c₀
  have hbetween :
      |mix.covariance F (fun m ↦ H m.1)| ≤ 2 * K * meanError := by
    exact FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
      weight mu F H main meanError K hmeanError hK hH hcommon
  have hwithin :
      |∑ c, weight.mass c *
        (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| ≤
        covError := by
    calc
      |∑ c, weight.mass c *
          (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| ≤
          ∑ c, |weight.mass c *
            (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, weight.mass c * covError := by
        apply Finset.sum_le_sum
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
        exact mul_le_mul_of_nonneg_left (hcellCov c) (weight.mass_nonneg c)
      _ = covError := by
        rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  have hcomponent (c : Cell Head) :
      (mu c).expect (fun x ↦ F ⟨c, x⟩ * G ⟨c, x⟩) =
        (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩) +
          (mu c).expect (fun x ↦ F ⟨c, x⟩) * H c := by
    unfold FiniteProbability.covariance H
    ring
  have htagProduct (c : Cell Head) :
      (mu c).expect (fun x ↦ F ⟨c, x⟩ * H c) =
        H c * (mu c).expect (fun x ↦ F ⟨c, x⟩) := by
    have hfun : (fun x ↦ F ⟨c, x⟩ * H c) =
        fun x ↦ H c * F ⟨c, x⟩ := by
      funext x
      ring
    rw [hfun, (mu c).expect_smul]
  have htagExpect (c : Cell Head) :
      (mu c).expect (fun _ ↦ H c) = H c := by
    unfold FiniteProbability.expect
    rw [← Finset.sum_mul, (mu c).mass_sum, one_mul]
  have hHdef (c : Cell Head) :
      (mu c).expect (fun x ↦ G ⟨c, x⟩) = H c := by
    rfl
  have hcross :
      (∑ c, weight.mass c *
        ((mu c).expect (fun x ↦ F ⟨c, x⟩) * H c)) =
      ∑ c, weight.mass c *
        (H c * (mu c).expect (fun x ↦ F ⟨c, x⟩)) := by
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hdecomp :
      mix.covariance F G =
        (∑ c, weight.mass c *
          (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)) +
          mix.covariance F (fun m ↦ H m.1) := by
    dsimp only [mix]
    unfold FiniteProbability.covariance
    simp_rw [FiniteProbability.sigmaMixture_expect]
    simp_rw [hcomponent, htagProduct, htagExpect, hHdef]
    simp only [add_sub_cancel_right]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    rw [hcross]
    ring
  have hmix : B.tiltedLaw xi = mix := by
    simpa only [mix, weight, mu] using B.tiltedLaw_eq_tiltedSigmaMixture xi
  rw [hmix, hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hwithin hbetween)





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (F G :
    Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) →
      Real)
  {covError meanError K : Real},
  LE.le.{0} (0 : Real) meanError →
    LE.le.{0} (0 : Real) K →
      (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
          LE.le.{0}
            (abs.{0}
              (Erdos390.Full.FiniteProbability.covariance.{0}
                (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c)
                  (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c))
                (fun x => F (Sigma.mk.{u_1, 0} c x)) fun x => G (Sigma.mk.{u_1, 0} c x)))
            covError) →
        (∀ (c c' : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.expect.{0}
                    (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c)
                      (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c))
                    fun x => F (Sigma.mk.{u_1, 0} c x))
                  (Erdos390.Full.FiniteProbability.expect.{0}
                    (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c')
                      (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c'))
                    fun x => F (Sigma.mk.{u_1, 0} c' x))))
              meanError) →
          (∀
              (m :
                Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
              LE.le.{0} (abs.{0} (G m)) K) →
            LE.le.{0}
              (abs.{0}
                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi) F G))
              (HAdd.hAdd.{0, 0, 0} covError (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) K) meanError)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
