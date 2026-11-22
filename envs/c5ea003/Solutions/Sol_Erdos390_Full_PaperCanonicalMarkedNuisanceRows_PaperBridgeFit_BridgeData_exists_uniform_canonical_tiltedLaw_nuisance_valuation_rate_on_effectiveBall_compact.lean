-- Prove2me | solution 1 for Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:19:12.277162+00:00
-- url     : https://prove2.me/submissions/3a914c70-190d-4cb3-8b16-79a160fe84f3

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_FiniteProbability_abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
import Theorems.Thm_Erdos390_Full_PaperCanonicalTiltedPrefixRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalTiltedValuationMeanRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted_compact



section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted : Erdos390.RemainingAnalyticGoal004_004.{u_1, u_2} := @Erdos390.Full.PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted : Erdos390.RemainingAnalyticGoal004_003.{u_1, u_2} := @Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted_compact
end
/- Source module: Erdos390.Full.FiniteTiltTV -/
section


/-!
# Total-variation control for finite exponential tilts

This supplies the normalization estimate used to compare each finite-`n`
tilted nuisance covariance with its own finite-`n` baseline.  The bound is
proved directly from the exponential density ratio.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]











theorem exponentialDeviation_nonneg (mu : FiniteProbability Omega)
    (S : Omega → ℝ) : 0 ≤ mu.exponentialDeviation S := by
  unfold exponentialDeviation expect
  exact Finset.sum_nonneg fun omega _ ↦
    mul_nonneg (mu.mass_nonneg omega) (abs_nonneg _)

theorem exponentialDeviation_le_two_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ)
    (hsmall : ∀ omega, |S omega| ≤ 1) :
    mu.exponentialDeviation S ≤
      2 * mu.expect (fun omega ↦ |S omega|) := by
  unfold exponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    mu.mass omega * |Real.exp (S omega) - 1| ≤
        mu.mass omega * (2 * |S omega|) :=
      mul_le_mul_of_nonneg_left
        (Real.abs_exp_sub_one_le (hsmall omega)) (mu.mass_nonneg omega)
    _ = 2 * (mu.mass omega * |S omega|) := by ring

theorem abs_expPartition_sub_one_le_deviation
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    |mu.expPartition S - 1| ≤ mu.exponentialDeviation S := by
  have hrewrite : mu.expPartition S - 1 =
      ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
    calc
      mu.expPartition S - 1 =
          (∑ omega, mu.mass omega * Real.exp (S omega)) -
            ∑ omega, mu.mass omega := by
              rw [expPartition, expect, mu.mass_sum]
      _ = ∑ omega,
          (mu.mass omega * Real.exp (S omega) - mu.mass omega) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
            apply Finset.sum_congr rfl
            intro omega _
            ring
  rw [hrewrite]
  calc
    |∑ omega, mu.mass omega * (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.exponentialDeviation S := by
      unfold exponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg omega)]

theorem expPartition_lower_bound
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    1 - mu.exponentialDeviation S ≤ mu.expPartition S := by
  have h := mu.abs_expPartition_sub_one_le_deviation S
  have hneg : -mu.exponentialDeviation S ≤
      -|mu.expPartition S - 1| := neg_le_neg h
  have habs : -|mu.expPartition S - 1| ≤
      mu.expPartition S - 1 := neg_abs_le _
  linarith





end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]









theorem expect_mono (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (hFG : ∀ omega, F omega ≤ G omega) : mu.expect F ≤ mu.expect G := by
  unfold expect
  apply Finset.sum_le_sum
  intro omega _
  exact mul_le_mul_of_nonneg_left (hFG omega) (mu.mass_nonneg omega)



















theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.OmittedScoreTilt -/
section


/-!
# Normalized marked-event bounds under an omitted-score tilt

The four-mark step in Lemma 7.5 first omits the forced local primes from
the score, estimates a marked numerator, and then divides by the tilted
partition function.  This file proves that normalization step for an actual
finite probability law.  The result keeps the marked and unmarked
exponential deviations separate, so a `1 / D` marked moment is not replaced
by an unscaled total-variation error.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]



theorem markedExponentialDeviation_nonneg
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    0 ≤ mu.markedExponentialDeviation A S := by
  unfold markedExponentialDeviation
  exact mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA omega) (abs_nonneg _)











/-- The marked numerator differs from its untilted value by at most the
marked exponential deviation. -/
theorem abs_expWeighted_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    |mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
        mu.expect A| ≤ mu.markedExponentialDeviation A S := by
  have hrearrange :
      mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
          mu.expect A =
        ∑ omega, mu.mass omega * A omega *
          (Real.exp (S omega) - 1) := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  rw [hrearrange]
  calc
    |∑ omega, mu.mass omega * A omega *
        (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * A omega *
          (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.markedExponentialDeviation A S := by
      unfold markedExponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_mul, abs_of_nonneg (mu.mass_nonneg omega),
        abs_of_nonneg (hA omega)]
      ring

/-- Exact normalization inequality for a marked event/statistic.  Unlike a
global total-variation estimate, the leading numerator error retains the
mark and hence its arithmetic `1 / D` scale. -/
theorem abs_exponentialTilt_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hdev : mu.exponentialDeviation S < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (mu.markedExponentialDeviation A S +
          mu.expect A * mu.exponentialDeviation S) /
        (1 - mu.exponentialDeviation S) := by
  let Z := mu.expPartition S
  let p := mu.expect A
  let N := mu.expect (fun omega ↦ A omega * Real.exp (S omega))
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have hZpos : 0 < Z := mu.expPartition_pos S
  have hdenpos : 0 < 1 - delta := sub_pos.mpr hdev
  have hZlower : 1 - delta ≤ Z := mu.expPartition_lower_bound S
  have hp0 : 0 ≤ p := mu.expect_nonneg A hA0
  have hp1 : p ≤ 1 := by
    calc
      p ≤ mu.expect (fun _ ↦ (1 : ℝ)) := mu.expect_mono A _ hA1
      _ = 1 := by simp [expect, mu.mass_sum]
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have heta0 : 0 ≤ eta :=
    mu.markedExponentialDeviation_nonneg A S hA0
  have hN : |N - p| ≤ eta := by
    exact mu.abs_expWeighted_expect_sub_expect_le A S hA0
  have hZ : |Z - 1| ≤ delta :=
    mu.abs_expPartition_sub_one_le_deviation S
  rw [mu.exponentialTilt_expect_eq A S]
  change |N / Z - p| ≤ (eta + p * delta) / (1 - delta)
  have hid : N / Z - p = ((N - p) + p * (1 - Z)) / Z := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hZpos]
  have hnum : |(N - p) + p * (1 - Z)| ≤ eta + p * delta := by
    calc
      |(N - p) + p * (1 - Z)| ≤
          |N - p| + |p * (1 - Z)| := abs_add_le _ _
      _ = |N - p| + p * |Z - 1| := by
        rw [abs_mul, abs_of_nonneg hp0, abs_sub_comm 1 Z]
      _ ≤ eta + p * delta := by
        exact add_le_add hN (mul_le_mul_of_nonneg_left hZ hp0)
  calc
    |(N - p) + p * (1 - Z)| / Z ≤
        (eta + p * delta) / Z :=
      div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (eta + p * delta) / (1 - delta) := by
      apply div_le_div_of_nonneg_left
      · exact add_nonneg heta0 (mul_nonneg hp0 hdelta0)
      · exact hdenpos
      · exact hZlower

/-- If the score itself is pointwise at most one, first marked and unmarked
absolute moments give a completely explicit version of the normalization
bound. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_small_score
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hsmall : ∀ omega, |S omega| ≤ 1)
    (htotal : 2 * mu.expect (fun omega ↦ |S omega|) < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let b := mu.expect (fun omega ↦ A omega * |S omega|)
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have ha0 : 0 ≤ a := mu.expect_nonneg _ fun omega ↦ abs_nonneg _
  have hb0 : 0 ≤ b := mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA0 omega) (abs_nonneg _)
  have hp0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have hdelta : delta ≤ 2 * a :=
    mu.exponentialDeviation_le_two_expect_abs S hsmall
  have hdelta1 : delta < 1 := hdelta.trans_lt htotal
  have heta : eta ≤ 2 * b := by
    unfold eta markedExponentialDeviation b expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega _
    calc
      mu.mass omega *
          (A omega * |Real.exp (S omega) - 1|) ≤
          mu.mass omega * (A omega * (2 * |S omega|)) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        exact mul_le_mul_of_nonneg_left
          (Real.abs_exp_sub_one_le (hsmall omega)) (hA0 omega)
      _ = 2 * (mu.mass omega * (A omega * |S omega|)) := by ring
  have hbase :=
    mu.abs_exponentialTilt_expect_sub_expect_le A S hA0 hA1 hdelta1
  refine hbase.trans ?_
  have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hdenA : 0 < 1 - 2 * a := sub_pos.mpr htotal
  apply (div_le_div_iff₀ hdenDelta hdenA).2
  have hnum : eta + mu.expect A * delta ≤
      2 * b + 2 * mu.expect A * a := by
    calc
      eta + mu.expect A * delta ≤
          2 * b + mu.expect A * (2 * a) :=
        add_le_add heta (mul_le_mul_of_nonneg_left hdelta hp0)
      _ = 2 * b + 2 * mu.expect A * a := by ring
  nlinarith



end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.TwoLocalRestoration -/
section


/-!
# Exact restoration of two omitted local primes

The omitted-score marked law is reweighted by the two literal local
valuation fugacities.  This file proves the exact finite identity connecting
that sequential reweighting to the full valuation tilt and then expands both
the marked numerator and the normalizer into prime-power indicators.
-/

open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel FiniteProbability ValuationScoreDomination
open LocalFugacity LocalFugacityRestoration ValuationCutoff

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Two finite probability objects are equal when their mass functions are
equal.  The remaining structure fields are propositions. -/
theorem eq_of_mass_eq (mu nu : FiniteProbability Omega)
    (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk muMass muNonneg muSum =>
      cases nu with
      | mk nuMass nuNonneg nuSum =>
          simp only [FiniteProbability.mk.injEq]
          exact h

/-- Exponential tilting first by `S` and then by `T` is exactly tilting once
by their sum. -/
theorem exponentialTilt_add (mu : FiniteProbability Omega)
    (S T : Omega → ℝ) :
    (mu.exponentialTilt S).exponentialTilt T =
      mu.exponentialTilt (fun omega ↦ S omega + T omega) := by
  apply eq_of_mass_eq
  funext omega
  have hpart :
      (mu.exponentialTilt S).expPartition T =
        mu.expPartition (fun x ↦ S x + T x) / mu.expPartition S := by
    unfold expPartition
    rw [mu.exponentialTilt_expect_eq (fun x ↦ Real.exp (T x)) S]
    congr 1
    unfold expect
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only
    rw [Real.exp_add]
    ring
  change
    (mu.mass omega * Real.exp (S omega) / mu.expPartition S) *
          Real.exp (T omega) /
        (mu.exponentialTilt S).expPartition T =
      mu.mass omega * Real.exp (S omega + T omega) /
        mu.expPartition (fun x ↦ S x + T x)
  rw [hpart]
  rw [Real.exp_add]
  field_simp [ne_of_gt (mu.expPartition_pos S),
    ne_of_gt (mu.expPartition_pos (fun x ↦ S x + T x))]



end FiniteProbability

namespace TwoLocalRestoration









section Cell

variable {S : Finset ℕ}





end Cell

end TwoLocalRestoration

end

end Erdos390.Full

end

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























theorem scaledBridgeScore_eq_medium_add_nuisance [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.scaledBridgeScore xi m =
      B.scaledMediumScore xi m + B.scaledNuisanceScore xi m := by
  rw [scaledBridgeScore, scaledMediumScore, scaledNuisanceScore,
    B.vectorScore_eq_effectivePrime_add_nuisance xi m]
  rw [add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring



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

/-- On each tagged cell the global score splits exactly into its medium
valuation part and the remaining physical/head part. -/
theorem sigmaCellScore_scaledBridge_eq [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledBridgeScore xi) c m =
      sigmaCellScore (B.scaledMediumScore xi) c m +
        sigmaCellScore (B.scaledNuisanceScore xi) c m := by
  exact B.scaledBridgeScore_eq_medium_add_nuisance xi ⟨c, m⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.LocalizedMarkedTiltCovariance -/
section


/-!
# Localized covariance stability under a small exponential tilt

The physical/head residual in the paper is a second, small tilt of each
medium-prime cell law.  A total-variation estimate would lose the divisibility
mark.  This file instead keeps the marginal and joint-event scales visible.

Everything below is an exact statement about finite probability laws.  The
arithmetic application supplies reciprocal bounds for the three marked
events `A`, `B`, and `A * B`.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]





theorem smallTiltLoss_le_eight_mul {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1) :
    smallTiltLoss epsilon ≤ 8 * epsilon := by
  have hden : 0 < 1 - 2 * epsilon := by nlinarith
  unfold smallTiltLoss
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg epsilon]

/-- A pointwise score of size `epsilon` changes a marked probability only
by the same relative scale.  In particular, an event of baseline probability
`O(1 / d)` changes by `O(epsilon / d)`, with no additive TV loss. -/
theorem abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    {epsilon a : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 2 * epsilon < 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      smallTiltLoss epsilon * a := by
  have hExpectAbs : mu.expect (fun omega ↦ |S omega|) ≤ epsilon := by
    calc
      mu.expect (fun omega ↦ |S omega|) ≤
          mu.expect (fun _ ↦ epsilon) := mu.expect_mono _ _ hscore
      _ = epsilon := by simp [expect, ← Finset.sum_mul, mu.mass_sum]
  have hAexpect0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have ha0 : 0 ≤ a := hAexpect0.trans hAexpect
  have hMarked :
      mu.expect (fun omega ↦ A omega * |S omega|) ≤ epsilon * a := by
    calc
      mu.expect (fun omega ↦ A omega * |S omega|) ≤
          mu.expect (fun omega ↦ A omega * epsilon) := by
        apply mu.expect_mono
        intro omega
        exact mul_le_mul_of_nonneg_left (hscore omega) (hA0 omega)
      _ = epsilon * mu.expect A := by
        rw [show (fun omega ↦ A omega * epsilon) =
            fun omega ↦ epsilon * A omega by
          funext omega
          ring]
        rw [mu.expect_smul]
      _ ≤ epsilon * a := mul_le_mul_of_nonneg_left hAexpect hepsilon
  have htotal : 2 * mu.expect (fun omega ↦ |S omega|) < 1 := by
    calc
      2 * mu.expect (fun omega ↦ |S omega|) ≤ 2 * epsilon :=
        mul_le_mul_of_nonneg_left hExpectAbs (by norm_num)
      _ < 1 := hsmall
  have hbase := mu.abs_exponentialTilt_expect_sub_expect_le_of_small_score
    A S hA0 hA1 (fun omega ↦ (hscore omega).trans (by linarith)) htotal
  have hdenActual : 0 < 1 - 2 * mu.expect (fun omega ↦ |S omega|) :=
    sub_pos.mpr htotal
  have hdenEpsilon : 0 < 1 - 2 * epsilon := sub_pos.mpr hsmall
  have hnum :
      2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|) ≤
        4 * epsilon * a := by
    have hsecond : mu.expect A * mu.expect (fun omega ↦ |S omega|) ≤
        a * epsilon :=
      mul_le_mul hAexpect hExpectAbs
        (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) ha0
    nlinarith
  refine hbase.trans ?_
  calc
    (2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) ≤
        (4 * epsilon * a) /
          (1 - 2 * mu.expect (fun omega ↦ |S omega|)) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (4 * epsilon * a) / (1 - 2 * epsilon) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg (by norm_num) hepsilon) ha0
      · exact hdenEpsilon
      · linarith
    _ = smallTiltLoss epsilon * a := by
      unfold smallTiltLoss
      field_simp









end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeNuisanceTiltFallback -/
section


/-!
# Marked fallback through the physical/head bridge tilt

On a fixed tagged bridge cell all centered-head coordinates are constant.
Consequently the residual nuisance tilt is exactly a small physical-log tilt;
the constant head factor cancels from normalization.  We combine that exact
identity with reciprocal divisibility bounds for the medium-prime tilt.

The resulting estimates retain the marked `1 / D` and `1 / (p q)` scales.
No total-variation estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination OmittedTiltFallback
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















private theorem sum_nuisanceCoord {I : Type*} [Fintype I]
    (f : NuisanceCoord I → ℝ) :
    (∑ z : NuisanceCoord I, f z) =
      f .physical + ∑ h : I, f (.head h) := by
  calc
    (∑ z : NuisanceCoord I, f z) =
        ∑ s : Unit ⊕ I, f ((nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback I).symm s) := by
      exact Fintype.sum_equiv (nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback I) f
        (fun s ↦ f ((nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback I).symm s)) (fun z ↦ by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback]

/-- The head part is literally constant on each tagged cell. -/
theorem sigmaCellScore_scaledNuisance_eq_physical_add_constant
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledNuisanceScore xi) c m =
      B.cellPhysicalTiltScore xi c m + B.cellHeadTiltConstant xi c := by
  unfold sigmaCellScore scaledNuisanceScore cellPhysicalTiltScore
    cellHeadTiltConstant
  rw [PiLp.inner_apply, sum_nuisanceCoord]
  simp only [B.nuisanceParameter_physical, B.nuisanceStatistic_physical,
    B.nuisanceParameter_head, B.nuisanceStatistic_head]
  unfold centeredHeadScore headIndicator StructuredSampleData.cellOf
  rw [add_div]
  congr 1
  · simp only [RCLike.inner_apply, conj_trivial]
    ring
  · apply congrArg (fun z : ℝ ↦ z / B.L)
    apply Finset.sum_congr rfl
    intro h hh
    split_ifs <;> simp only [RCLike.inner_apply, conj_trivial] <;> ring

private theorem exponentialTilt_const
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (k : ℝ) :
    mu.exponentialTilt (fun _ ↦ k) = mu := by
  apply FiniteProbability.eq_of_mass_eq
  funext omega
  have hpart : mu.expPartition (fun _ ↦ k) = Real.exp k := by
    unfold expPartition expect
    calc
      (∑ x, mu.mass x * Real.exp k) =
          (∑ x, mu.mass x) * Real.exp k := by rw [Finset.sum_mul]
      _ = Real.exp k := by rw [mu.mass_sum, one_mul]
  change mu.mass omega * Real.exp k /
      mu.expPartition (fun _ ↦ k) = mu.mass omega
  rw [hpart]
  field_simp [ne_of_gt (Real.exp_pos k)]

/-- Adding the constant cell-head factor does not change a normalized
exponential tilt. -/
theorem exponentialTilt_cellNuisance_eq_physical [Nonempty Head]
    (c : Cell Head)
    (mu : FiniteProbability (B.sampleData.SampleAt c))
    (xi : B.ParamSpace) :
    mu.exponentialTilt
        (sigmaCellScore (B.scaledNuisanceScore xi) c) =
      mu.exponentialTilt (B.cellPhysicalTiltScore xi c) := by
  have hscore : sigmaCellScore (B.scaledNuisanceScore xi) c =
      fun m ↦ B.cellPhysicalTiltScore xi c m +
        B.cellHeadTiltConstant xi c := by
    funext m
    exact B.sigmaCellScore_scaledNuisance_eq_physical_add_constant xi c m
  rw [hscore, ← mu.exponentialTilt_add]
  rw [exponentialTilt_const]

/-- Exact component-law factorization: full bridge tilt equals medium tilt
followed by the small physical tilt. -/
theorem guardedCell_fullTilt_eq_medium_physicalTilt [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.guardedCellProbability c).exponentialTilt
        (sigmaCellScore (B.scaledBridgeScore xi) c) =
      (B.cellMediumLaw xi c).exponentialTilt
        (B.cellPhysicalTiltScore xi c) := by
  have hscore : sigmaCellScore (B.scaledBridgeScore xi) c =
      fun m ↦ sigmaCellScore (B.scaledMediumScore xi) c m +
        sigmaCellScore (B.scaledNuisanceScore xi) c m := by
    funext m
    exact B.sigmaCellScore_scaledBridge_eq xi c m
  rw [hscore, ← (B.guardedCellProbability c).exponentialTilt_add]
  exact B.exponentialTilt_cellNuisance_eq_physical
    c (B.cellMediumLaw xi c) xi

/-- The actual guard-deleted cell endpoint is positive. -/
theorem cell_hi_pos (c : Cell Head) :
    0 < B.sampleData.hi c.2 := by
  obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
  let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
  have hmle : m ≤ B.sampleData.hi c.2 := by
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hmpos : 0 < m := by
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  exact hmpos.trans_le hmle



/-- A fixed physical interval and a bounded physical parameter make the
second tilt pointwise `O(1/L)`. -/
theorem abs_cellPhysicalTiltScore_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {Aphys Kphys : ℝ}
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys) :
    ∀ m, |B.cellPhysicalTiltScore xi c m| ≤
      Aphys * Kphys / B.L := by
  intro m
  unfold cellPhysicalTiltScore
  rw [abs_mul, abs_div, abs_of_pos B.L_pos]
  calc
    (|xi MomentCoord.physical| / B.L) *
        |B.physicalScore ⟨c, m⟩| ≤
      (Aphys / B.L) * Kphys := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hAphys B.L_pos.le
        · exact hKphys m
        · exact abs_nonneg _
        · exact div_nonneg (le_trans (abs_nonneg _) hAphys) B.L_pos.le
    _ = Aphys * Kphys / B.L := by ring

/-- The abstract physical-score bound above is discharged by the literal
fixed intervals and their canonical floored endpoints.  In particular the
constant is `log U`, independent of `n` and of the later tilt box. -/
theorem abs_cellPhysicalTiltScore_le_fixedIntervals [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (I : PaperGuardCensus.PhysicalIntervals) {U Aphys : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys) :
    ∀ m, |B.cellPhysicalTiltScore xi c m| ≤
      Aphys * Real.log U / B.L := by
  apply B.abs_cellPhysicalTiltScore_le xi c hAphys
  intro m
  exact B.abs_physicalScore_le_log_upperBound I
    hlowerOne hupperU hlo hhi ⟨c, m⟩





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























/-- A componentwise common expectation profile gives a global covariance
bound against every bounded head function.  The globally tilted cell weights
are the exact partition-function-reweighted weights; no baseline-weight
replacement is made here. -/
theorem abs_tiltedLaw_covariance_headFunction_le_of_common_cell_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (phi : Head → ℝ) (main error K : ℝ)
    (herror : 0 ≤ error) (hK : 0 ≤ K)
    (hphi : ∀ h, |phi h| ≤ K)
    (hcell : ∀ c : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) - main| ≤ error) :
    |(B.tiltedLaw xi).covariance F (B.headFunctionScore phi)| ≤
      2 * K * error := by
  rw [B.tiltedLaw_eq_tiltedSigmaMixture xi]
  exact FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
      (FiniteProbability.tiltedSigmaWeight
        B.baselineCellProbability B.guardedCellProbability
        (B.scaledBridgeScore xi))
      (fun c ↦ (B.guardedCellProbability c).exponentialTilt
        (FiniteProbability.sigmaCellScore (B.scaledBridgeScore xi) c))
      F (fun c ↦ phi c.1) main error K herror hK
      (fun c ↦ hphi c.1) hcell







theorem headFunctionScore_centeredHeadTagFunction
    [Nonempty Head] (h : B.HeadIndex) :
    B.headFunctionScore (B.centeredHeadTagFunction h) =
      B.centeredHeadScore h := by
  funext m
  unfold headFunctionScore centeredHeadTagFunction centeredHeadScore
    headIndicator
  rfl

theorem abs_centeredHeadTagFunction_le_three
    [Nonempty Head] (h : B.HeadIndex) (h₀ : Head) :
    |B.centeredHeadTagFunction h h₀| ≤ 3 := by
  have hbase0 : 0 ≤ B.headBaselineMass h.1 :=
    PaperStatisticNorm.BridgeData.headBaselineMass_nonneg B h.1
  have hbase2 : B.headBaselineMass h.1 ≤ 2 :=
    PaperStatisticNorm.BridgeData.headBaselineMass_le_two B h.1
  unfold centeredHeadTagFunction
  split_ifs
  all_goals rw [abs_le]
  all_goals constructor <;> linarith

/-- Pairwise agreement of the exact component means is enough for the
literal centered head coordinate.  A reference component supplies the
`main` in the common-profile mixture identity, so no limiting component
weights and no independently postulated head covariance row occur in the
statement. -/
theorem abs_tiltedLaw_covariance_nuisanceHead_le_of_pairwise_cell_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (h : B.HeadIndex) {error : ℝ} (herror : 0 ≤ error)
    (hpair : ∀ c c' : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ F ⟨c', x⟩)| ≤ error) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m (NuisanceCoord.head h)) F| ≤
      6 * error := by
  let c₀ : Cell Head := (Classical.choice inferInstance, PhysicalSign.minus)
  let main : ℝ :=
    ((B.guardedCellProbability c₀).exponentialTilt
      (FiniteProbability.sigmaCellScore
        (B.scaledBridgeScore xi) c₀)).expect (fun x ↦ F ⟨c₀, x⟩)
  have hcommon : ∀ c : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) - main| ≤ error := by
    intro c
    exact hpair c c₀
  have hraw := B.abs_tiltedLaw_covariance_headFunction_le_of_common_cell_expect
    xi F (B.centeredHeadTagFunction h) main error 3 herror (by norm_num)
    (B.abs_centeredHeadTagFunction_le_three h) hcommon
  have hcoord :
      (fun m ↦ B.nuisanceStatistic m (NuisanceCoord.head h)) =
        B.centeredHeadScore h := by
    funext m
    exact B.nuisanceStatistic_head m h
  rw [(B.tiltedLaw xi).covariance_comm]
  rw [hcoord]
  rw [← B.headFunctionScore_centeredHeadTagFunction h]
  convert hraw using 1
  ring

/-- The paper's full nuisance marked family is a consequence of exactly two
analytic inputs: the physical marked row and pairwise agreement of the
component valuation means.  The head coordinates are discharged internally
by the preceding finite-mixture cancellation. -/
theorem abs_tiltedLaw_covariance_nuisanceCoord_le_of_pairwise_cell_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    {error : ℝ} (herror : 0 ≤ error)
    (hphysical :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical) F| ≤
        6 * error)
    (hpair : ∀ c c' : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ F ⟨c', x⟩)| ≤ error) :
    ∀ z : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z) F| ≤ 6 * error := by
  intro z
  cases z with
  | physical => exact hphysical
  | head h =>
      exact B.abs_tiltedLaw_covariance_nuisanceHead_le_of_pairwise_cell_expect
        xi F h herror hpair

/-- Reciprocal-scale specialization for the actual medium-prime valuation
family.  This is the finite statement corresponding to the paper's
`O(1/(pL))` nuisance marked family: the physical Stieltjes row and the
pairwise exact-cell comparison are the only analytic hypotheses. -/
theorem nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
    [Nonempty Head]
    (xi : B.ParamSpace) {Cscale Lscale : ℝ}
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ))) :
    ∀ (z : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (6 * Cscale / Lscale) * (1 / (p.1 : ℝ)) := by
  intro z p
  let error : ℝ := (Cscale / Lscale) * (1 / (p.1 : ℝ))
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have herror : 0 ≤ error :=
    mul_nonneg (div_nonneg hCscale hLscale.le) (one_div_nonneg.mpr hp.le)
  have hphysical' :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        6 * error := by
    exact (hphysical p).trans (by nlinarith)
  have hrows := B.abs_tiltedLaw_covariance_nuisanceCoord_le_of_pairwise_cell_expect
    xi (fun m ↦ valuation p.1 (B.sampleData.value m)) herror hphysical'
    (fun c c' ↦ hpair p c c') z
  change |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m z)
      (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤ _ at hrows
  calc
    |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m z)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        6 * error := hrows
    _ = (6 * Cscale / Lscale) * (1 / (p.1 : ℝ)) := by
      dsimp only [error]
      ring

/-- The global physical marked row is itself a consequence of the literal
within-cell Stieltjes covariance estimate and the same pairwise component
mean comparison used for the head rows.  This is the exact law-of-total-
covariance attachment: no global physical-row estimate is postulated. -/
theorem nuisanceMarkedRows_le_of_cell_physical_covariance_and_pairwise_valuation
    [Nonempty Head]
    (xi : B.ParamSpace) {Cscale Lscale K : ℝ}
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale) (hK : 0 ≤ K)
    (hphysicalBound : ∀ m : B.sampleData.Sample,
      |B.physicalScore m| ≤ K)
    (hcellPhysical : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).covariance
          (fun x ↦ valuation p.1 (x : ℕ))
          (fun x ↦ B.physicalScore ⟨c, x⟩)| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ))) :
    ∀ (z : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (6 * ((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by
  have hCfull : 0 ≤ (1 + 2 * K) * Cscale := by positivity
  have hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (((1 + 2 * K) * Cscale) / Lscale) * (1 / (p.1 : ℝ)) := by
    intro p
    let error : ℝ := (Cscale / Lscale) * (1 / (p.1 : ℝ))
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have herror : 0 ≤ error :=
      mul_nonneg (div_nonneg hCscale hLscale.le)
        (one_div_nonneg.mpr hp.le)
    have hraw :=
      B.abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
        xi
        (fun m ↦ valuation p.1 (B.sampleData.value m))
        B.physicalScore herror hK
        (fun c ↦ hcellPhysical p c)
        (fun c c' ↦ hpair p c c') hphysicalBound
    have hcoord :
        (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical) =
          B.physicalScore := by
      funext m
      exact B.nuisanceStatistic_physical m
    rw [hcoord]
    calc
      |(B.tiltedLaw xi).covariance B.physicalScore
          (fun m ↦ valuation p.1 (B.sampleData.value m))| =
          |(B.tiltedLaw xi).covariance
            (fun m ↦ valuation p.1 (B.sampleData.value m))
            B.physicalScore| := by
        rw [(B.tiltedLaw xi).covariance_comm]
      _ ≤ error + 2 * K * error := hraw
      _ = (((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by
        dsimp only [error]
        ring
  have hpairFull : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by
    intro p c c'
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hsmall := hpair p c c'
    have hfactor : (1 : ℝ) ≤ 1 + 2 * K := by linarith
    have hbase : 0 ≤ (Cscale / Lscale) * (1 / (p.1 : ℝ)) :=
      mul_nonneg (div_nonneg hCscale hLscale.le)
        (one_div_nonneg.mpr hp.le)
    calc
      |((B.guardedCellProbability c).exponentialTilt
            (FiniteProbability.sigmaCellScore
              (B.scaledBridgeScore xi) c)).expect
            (fun x ↦ valuation p.1 (x : ℕ)) -
          ((B.guardedCellProbability c').exponentialTilt
            (FiniteProbability.sigmaCellScore
              (B.scaledBridgeScore xi) c')).expect
            (fun x ↦ valuation p.1 (x : ℕ))| ≤
          (Cscale / Lscale) * (1 / (p.1 : ℝ)) := hsmall
      _ ≤ (1 + 2 * K) *
          ((Cscale / Lscale) * (1 / (p.1 : ℝ))) :=
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hfactor hbase)
      _ = (((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by ring
  exact B.nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
    xi hCfull hLscale hphysical hpairFull





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteLogStieltjes -/
section


/-!
# Finite logarithmic Stieltjes transfer

The physical column in the marked smooth-number argument is obtained from
uniform prefix-count estimates by Abel summation.  This file isolates the
exact deterministic step.  In particular, the error is charged only once
against the total variation of `log`; it is not multiplied by the number of
integer endpoints or by an auxiliary partition size.
-/

open scoped BigOperators Interval

namespace Erdos390.Full.FiniteLogStieltjes

open Finset MeasureTheory Set

noncomputable section

variable {Omega : Type*} [Fintype Omega]



/-- Summing the centered fiber masses over a finite set is exactly the
centered expectation of its value-preimage. -/
theorem sum_centeredFiberMass_eq
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) (s : Finset ℕ) :
    (∑ k ∈ s, centeredFiberMass mu value A k) =
      ∑ omega, if value omega ∈ s then
        mu.mass omega * (A omega - mu.expect A) else 0 := by
  unfold centeredFiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hv : value omega ∈ s
  · rw [if_pos hv]
    rw [Finset.sum_eq_single (value omega)]
    · simp
    · intro k hk hne
      simp [hne.symm]
    · exact fun h ↦ (h hv).elim
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : value omega ≠ k := by
      intro h
      apply hv
      simpa [h] using hk
    simp [hne]

theorem sum_centeredFiberMass_Icc_lo_eq_zero
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {lo : ℕ}
    (hlo : ∀ omega, lo < value omega) :
    ∑ k ∈ Icc 0 lo, centeredFiberMass mu value A k = 0 := by
  rw [sum_centeredFiberMass_eq]
  apply Finset.sum_eq_zero
  intro omega homega
  rw [if_neg]
  intro hmem
  exact (not_le_of_gt (hlo omega)) (Finset.mem_Icc.mp hmem).2

theorem sum_centeredFiberMass_Icc_hi_eq_zero
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {hi : ℕ}
    (hhi : ∀ omega, value omega ≤ hi) :
    ∑ k ∈ Icc 0 hi, centeredFiberMass mu value A k = 0 := by
  rw [sum_centeredFiberMass_eq]
  have hmem (omega : Omega) : value omega ∈ Finset.Icc 0 hi :=
    Finset.mem_Icc.mpr ⟨Nat.zero_le _, hhi omega⟩
  have hremove : (∑ omega, if value omega ∈ Finset.Icc 0 hi then
      mu.mass omega * (A omega - mu.expect A) else 0) =
      ∑ omega, mu.mass omega * (A omega - mu.expect A) := by
    apply Finset.sum_congr rfl
    intro omega homega
    rw [if_pos (hmem omega)]
  rw [hremove]
  unfold FiniteProbability.expect
  calc
    (∑ omega, mu.mass omega *
        (A omega - ∑ eta, mu.mass eta * A eta)) =
        ∑ omega, (mu.mass omega * A omega -
          mu.mass omega * (∑ eta, mu.mass eta * A eta)) := by
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega, mu.mass omega * A omega) -
        (∑ omega, mu.mass omega *
          (∑ eta, mu.mass eta * A eta)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ omega, mu.mass omega * A omega) -
        (∑ omega, mu.mass omega) *
          (∑ eta, mu.mass eta * A eta) := by
      rw [← Finset.sum_mul]
    _ = 0 := by
      rw [mu.mass_sum]
      ring

/-- The log-weighted centered fiber sum is the literal covariance with the
integer logarithm. -/
theorem sum_log_centeredFiberMass_eq_covariance
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {lo hi : ℕ}
    (hsupport : ∀ omega, lo < value omega ∧ value omega ≤ hi) :
    (∑ k ∈ Ioc lo hi,
        Real.log (k : ℝ) * centeredFiberMass mu value A k) =
      mu.covariance A (fun omega ↦ Real.log (value omega : ℝ)) := by
  unfold centeredFiberMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (omega : Omega) :
      (∑ k ∈ Ioc lo hi,
          Real.log (k : ℝ) *
            (if value omega = k then
              mu.mass omega * (A omega - mu.expect A) else 0)) =
        Real.log (value omega : ℝ) *
          (mu.mass omega * (A omega - mu.expect A)) := by
    rw [Finset.sum_eq_single (value omega)]
    · simp
    · intro k hk hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (Finset.mem_Ioc.mpr (hsupport omega))).elim
  simp_rw [hinner]
  unfold FiniteProbability.covariance FiniteProbability.expect
  calc
    (∑ omega,
        Real.log (value omega : ℝ) *
          (mu.mass omega *
            (A omega - ∑ eta, mu.mass eta * A eta))) =
      ∑ omega,
        (mu.mass omega * (A omega * Real.log (value omega : ℝ)) -
          (∑ eta, mu.mass eta * A eta) *
            (mu.mass omega * Real.log (value omega : ℝ))) := by
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega,
        mu.mass omega * (A omega * Real.log (value omega : ℝ))) -
        (∑ omega, (∑ eta, mu.mass eta * A eta) *
          (mu.mass omega * Real.log (value omega : ℝ))) :=
      by rw [Finset.sum_sub_distrib]
    _ = (∑ omega,
        mu.mass omega * (A omega * Real.log (value omega : ℝ))) -
      (∑ eta, mu.mass eta * A eta) *
        (∑ omega, mu.mass omega * Real.log (value omega : ℝ)) := by
      rw [← Finset.mul_sum]

/-- A centered finite sequence whose every prefix is bounded by `E` has a
logarithmically weighted sum bounded by a fixed physical-interval constant.
The two endpoint hypotheses are the exact centered-mass cancellations used
in the covariance application. -/
theorem abs_sum_log_mul_le_of_prefix_bound
    (c : ℕ → ℝ) {lo hi : ℕ} {E : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hE : 0 ≤ E)
    (hprefixLo : ∑ k ∈ Icc 0 lo, c k = 0)
    (hprefixHi : ∑ k ∈ Icc 0 hi, c k = 0)
    (hprefix : ∀ t ∈ Set.Ioc (lo : ℝ) (hi : ℝ),
      |∑ k ∈ Icc 0 ⌊t⌋₊, c k| ≤ E) :
    |∑ k ∈ Ioc lo hi, Real.log (k : ℝ) * c k| ≤
      (E / (lo : ℝ)) * ((hi : ℝ) - (lo : ℝ)) := by
  have hloR : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) < (hi : ℝ) := hloR.trans_le (by exact_mod_cast hlohi)
  have hdiff : ∀ t ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      DifferentiableAt ℝ Real.log t := by
    intro t ht
    exact Real.differentiableAt_log (ne_of_gt (hloR.trans_le ht.1))
  have hint : IntegrableOn (deriv Real.log)
      (Set.Icc (lo : ℝ) (hi : ℝ)) := by
    rw [Real.deriv_log']
    exact ((continuousOn_inv₀ (G₀ := ℝ)).mono fun t ht ↦
      Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (hloR.trans_le ht.1))).integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    c hlohi hdiff hint
  rw [hprefixLo, hprefixHi, mul_zero, mul_zero] at hAbel
  simp only [neg_zero, zero_sub] at hAbel
  rw [hAbel, abs_neg]
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hlohi)]
  have hbound : ∀ t ∈ Ι (lo : ℝ) (hi : ℝ),
      ‖deriv Real.log t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ E / (lo : ℝ) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc (lo : ℝ) (hi : ℝ) := by
      rw [Set.uIoc_of_le (by exact_mod_cast hlohi)] at ht
      exact ht
    have htpos : 0 < t := hloR.trans htIoc.1
    have hpref := hprefix t htIoc
    rw [Real.deriv_log, Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos htpos]
    have hinv : t⁻¹ ≤ ((lo : ℝ))⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le hloR htIoc.1.le)
    calc
      t⁻¹ * |∑ k ∈ Icc 0 ⌊t⌋₊, c k| ≤ t⁻¹ * E :=
        mul_le_mul_of_nonneg_left hpref (inv_nonneg.mpr htpos.le)
      _ ≤ ((lo : ℝ))⁻¹ * E :=
        mul_le_mul_of_nonneg_right hinv hE
      _ = E / (lo : ℝ) := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hsub : 0 ≤ (hi : ℝ) - (lo : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hlohi)
  simpa [abs_of_nonneg hsub] using hnorm

end

end Erdos390.Full.FiniteLogStieltjes

end

/- Source module: Erdos390.Full.PaperBridgePhysicalValuationRow -/
section


/-!
# The physical-log column through the residual bridge tilt

The medium-prime Stieltjes estimate in the paper gives a reciprocal-scale
bound for `Cov(v_p,R)` inside each structured cell.  The full bridge law has
one further physical tilt of size `O(1/L)`.  This file proves that the latter
operation preserves the `1/p` scale for the *full valuation* column.

The proof uses the actual bounded valuation and the fixed physical interval.
The artificial pointwise valuation cutoff cancels after normalization, so the
conclusion depends only on the reciprocal first moment.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus FiniteProbability
open PrimePowerCovariance PrimePowerCutoffCovariance
open ValuationCutoff LocalFugacityBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The common endpoint is a strictly positive pointwise bound for every
actual valuation on every guarded bridge cell. -/
theorem valuation_le_sampleEndpoint
    (c : Cell Head) (p : ℕ) (m : B.sampleData.SampleAt c) :
    valuation p (m : ℕ) ≤ (B.sampleEndpoint : ℝ) := by
  have hmpos : 0 < (m : ℕ) := by
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  have hmend : (m : ℕ) ≤ B.sampleEndpoint := by
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample
  unfold valuation
  exact_mod_cast ((Nat.factorization_lt p hmpos.ne').le.trans hmend)

theorem sampleEndpoint_pos (c : Cell Head) : 0 < B.sampleEndpoint := by
  exact (B.cell_hi_pos c).trans_le (by
    cases c.2 <;> simp [sampleEndpoint])

















/-- A small physical residual tilt changes the *full valuation* expectation
at relative reciprocal scale.  The proof normalizes by the actual finite
cell endpoint, applies the marked small-tilt estimate, and then cancels that
endpoint exactly; hence no artificial pointwise cutoff remains in the
conclusion. -/
theorem abs_guardedCell_fullTilt_expect_valuation_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {epsilon Aval : ℝ} {p : ℕ}
    (hp : 0 < p) (hepsilon0 : 0 ≤ epsilon) (hAval0 : 0 ≤ Aval)
    (hscore : ∀ m : B.sampleData.SampleAt c,
      |B.cellPhysicalTiltScore xi c m| ≤ epsilon)
    (hVexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * epsilon ≤ 1) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      8 * epsilon * (Aval / (p : ℝ)) := by
  let M : ℝ := B.sampleEndpoint
  let V : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ valuation p (m : ℕ)
  let A : B.sampleData.SampleAt c → ℝ := fun m ↦ V m / M
  let a : ℝ := Aval / (p : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast B.sampleEndpoint_pos c
  have hV0 : ∀ m, 0 ≤ V m := fun m ↦ valuation_nonneg p (m : ℕ)
  have hVM : ∀ m, V m ≤ M := by
    intro m
    simpa only [V, M] using B.valuation_le_sampleEndpoint c p m
  have hA0 : ∀ m, 0 ≤ A m := fun m ↦ div_nonneg (hV0 m) hM.le
  have hA1 : ∀ m, A m ≤ 1 := by
    intro m
    exact (div_le_one hM).2 (hVM m)
  have ha0 : 0 ≤ a := div_nonneg hAval0 (by exact_mod_cast hp.le)
  have hAexpect : (B.cellMediumLaw xi c).expect A ≤ a / M := by
    have hscale : A = fun m ↦ (1 / M) * V m := by
      funext m
      dsimp only [A]
      ring
    rw [hscale, (B.cellMediumLaw xi c).expect_smul]
    calc
      (1 / M) * (B.cellMediumLaw xi c).expect V =
          (B.cellMediumLaw xi c).expect V / M := by ring
      _ ≤ a / M := div_le_div_of_nonneg_right
        (by simpa only [V, a] using hVexpect) hM.le
  have hsmallTwo : 2 * epsilon < 1 := by nlinarith
  have hraw :=
    FiniteProbability.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (B.cellMediumLaw xi c) A (B.cellPhysicalTiltScore xi c)
      hA0 hA1 hepsilon0 hsmallTwo hscore hAexpect
  rw [← B.guardedCell_fullTilt_eq_medium_physicalTilt xi c] at hraw
  have hloss : smallTiltLoss epsilon ≤ 8 * epsilon :=
    smallTiltLoss_le_eight_mul hepsilon0 hsmall
  have hfactor0 : 0 ≤ a / M := div_nonneg ha0 hM.le
  have hscaled :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).expect A -
          (B.cellMediumLaw xi c).expect A| ≤
        8 * epsilon * (a / M) :=
    hraw.trans (mul_le_mul_of_nonneg_right hloss hfactor0)
  have hExpect (mu : FiniteProbability (B.sampleData.SampleAt c)) :
      mu.expect A = (1 / M) * mu.expect V := by
    have hscale : A = fun m ↦ (1 / M) * V m := by
      funext m
      dsimp only [A]
      ring
    rw [hscale, mu.expect_smul]
  rw [hExpect, hExpect] at hscaled
  have hdiv :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
          (B.cellMediumLaw xi c).expect V| / M ≤
        (8 * epsilon * a) / M := by
    calc
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
          (B.cellMediumLaw xi c).expect V| / M =
          |(1 / M) *
              ((B.guardedCellProbability c).exponentialTilt
                (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
            (1 / M) * (B.cellMediumLaw xi c).expect V| := by
        rw [show |((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
            (B.cellMediumLaw xi c).expect V| / M =
          |(((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
            (B.cellMediumLaw xi c).expect V) / M| by
              rw [abs_div, abs_of_pos hM]]
        apply congrArg abs
        field_simp [ne_of_gt hM]
      _ ≤ 8 * epsilon * (a / M) := hscaled
      _ = (8 * epsilon * a) / M := by ring
  have hmain := (div_le_div_iff_of_pos_right hM).mp hdiv
  simpa only [V, a] using hmain

/-- Pairwise component-mean agreement survives the physical residual tilt
at the same reciprocal scale.  Both endpoint losses are included, so the
constant is exactly `16 * epsilon * Aval / p` in addition to the medium-law
pairwise error. -/
theorem abs_guardedCell_fullTilt_expect_valuation_sub_other_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c c' : Cell Head)
    {epsilon Aval meanError : ℝ} {p : ℕ}
    (hp : 0 < p) (hepsilon0 : 0 ≤ epsilon) (hAval0 : 0 ≤ Aval)
    (hscore : ∀ (d : Cell Head) (m : B.sampleData.SampleAt d),
      |B.cellPhysicalTiltScore xi d m| ≤ epsilon)
    (hVexpect : ∀ d : Cell Head, (B.cellMediumLaw xi d).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * epsilon ≤ 1)
    (hmediumPair :
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p (m : ℕ))| ≤ meanError) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p (m : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      meanError + 16 * epsilon * (Aval / (p : ℝ)) := by
  let Fc : ℝ :=
    ((B.guardedCellProbability c).exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
      (fun m ↦ valuation p (m : ℕ))
  let Mc : ℝ := (B.cellMediumLaw xi c).expect
    (fun m ↦ valuation p (m : ℕ))
  let Fc' : ℝ :=
    ((B.guardedCellProbability c').exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
      (fun m ↦ valuation p (m : ℕ))
  let Mc' : ℝ := (B.cellMediumLaw xi c').expect
    (fun m ↦ valuation p (m : ℕ))
  have hc : |Fc - Mc| ≤ 8 * epsilon * (Aval / (p : ℝ)) := by
    simpa only [Fc, Mc] using
      B.abs_guardedCell_fullTilt_expect_valuation_sub_medium_le
        xi c hp hepsilon0 hAval0 (hscore c) (hVexpect c) hsmall
  have hc' : |Fc' - Mc'| ≤ 8 * epsilon * (Aval / (p : ℝ)) := by
    simpa only [Fc', Mc'] using
      B.abs_guardedCell_fullTilt_expect_valuation_sub_medium_le
        xi c' hp hepsilon0 hAval0 (hscore c') (hVexpect c') hsmall
  change |Fc - Fc'| ≤ _
  calc
    |Fc - Fc'| = |(Fc - Mc) + (Mc - Mc') + (Mc' - Fc')| := by
      congr 1
      ring
    _ ≤ |Fc - Mc| + |Mc - Mc'| + |Mc' - Fc'| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ 8 * epsilon * (Aval / (p : ℝ)) + meanError +
        8 * epsilon * (Aval / (p : ℝ)) := by
      exact add_le_add
        (add_le_add hc (by simpa only [Mc, Mc'] using hmediumPair))
        (by simpa only [abs_sub_comm] using hc')
    _ = meanError + 16 * epsilon * (Aval / (p : ℝ)) := by ring



/-- The full-tilt cell covariance bound obtained by combining the medium-law
Stieltjes row with the preceding residual-tilt stability theorem.  The
coefficient of `1 / (p L)` is displayed exactly, with no hidden dependence on
the later tilt box. -/
theorem abs_guardedCell_fullTilt_covariance_valuation_physical_le_of_medium
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (I : PhysicalIntervals) {U Aphys Aval Cmedium : ℝ} {p : ℕ}
    (hp : 0 < p)
    (hAphys0 : 0 ≤ Aphys) (hAval0 : 0 ≤ Aval)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hVexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * (Aphys * Real.log U / B.L) ≤ 1)
    (hmedium :
      |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
          (Cmedium / B.L) * (1 / (p : ℝ))) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ valuation p (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      ((Cmedium + 32 * Real.log U * Aphys * Real.log U * Aval) / B.L) *
        (1 / (p : ℝ)) := by
  let full : ℝ :=
    ((B.guardedCellProbability c).exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
      (fun m ↦ valuation p (m : ℕ))
      (fun m ↦ B.physicalScore ⟨c, m⟩)
  let medium : ℝ := (B.cellMediumLaw xi c).covariance
    (fun m ↦ valuation p (m : ℕ))
    (fun m ↦ B.physicalScore ⟨c, m⟩)
  have htilt :=
    B.abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
      xi c I hp hAphys0 hAval0 hlowerOne hupperU hlo hhi hAphys
      hVexpect hsmall
  have htriangle : |full| ≤ |full - medium| + |medium| := by
    have h := abs_add_le (full - medium) medium
    simpa only [sub_add_cancel] using h
  calc
    |full| ≤ |full - medium| + |medium| := htriangle
    _ ≤ 32 * Real.log U * (Aphys * Real.log U / B.L) *
          (Aval / (p : ℝ)) +
        (Cmedium / B.L) * (1 / (p : ℝ)) :=
      add_le_add (by simpa only [full, medium] using htilt) hmedium
    _ = ((Cmedium + 32 * Real.log U * Aphys * Real.log U * Aval) / B.L) *
        (1 / (p : ℝ)) := by ring

/-- Uniform family form of the two preceding residual-tilt attachments.
The only analytic inputs left are the medium-law Stieltjes covariance and
medium-law pairwise valuation profile.  The resulting full-tilt cell
covariance and pairwise mean comparison share one explicit structural
coefficient. -/
theorem fullTiltCellProfiles_of_medium_stieltjes
    [Nonempty Head]
    (xi : B.ParamSpace) (I : PhysicalIntervals)
    {U Aphys Aval Ccov Cmean : ℝ}
    (hAphys0 : 0 ≤ Aphys) (hAval0 : 0 ≤ Aval)
    (hCcov : 0 ≤ Ccov) (hCmean : 0 ≤ Cmean)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hVexpect : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      (B.cellMediumLaw xi c).expect
        (fun m ↦ valuation p.1 (m : ℕ)) ≤ Aval / (p.1 : ℝ))
    (hsmall : 8 * (Aphys * Real.log U / B.L) ≤ 1)
    (hmediumCov : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p.1 (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
          (Ccov / B.L) * (1 / (p.1 : ℝ)))
    (hmediumPair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p.1 (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p.1 (m : ℕ))| ≤
        (Cmean / B.L) * (1 / (p.1 : ℝ))) :
    let Cfull := Ccov + Cmean +
      32 * Real.log U * Aphys * Real.log U * Aval +
      16 * Aphys * Real.log U * Aval
    (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
        (Cfull / B.L) * (1 / (p.1 : ℝ))) ∧
    (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p.1 (m : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
          (fun m ↦ valuation p.1 (m : ℕ))| ≤
        (Cfull / B.L) * (1 / (p.1 : ℝ))) := by
  dsimp only
  let Cfull : ℝ := Ccov + Cmean +
    32 * Real.log U * Aphys * Real.log U * Aval +
    16 * Aphys * Real.log U * Aval
  have hU : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hlogU : 0 ≤ Real.log U := (Real.log_pos hU).le
  have hscore : ∀ (c : Cell Head) (m : B.sampleData.SampleAt c),
      |B.cellPhysicalTiltScore xi c m| ≤
        Aphys * Real.log U / B.L := by
    intro c m
    exact B.abs_cellPhysicalTiltScore_le_fixedIntervals
      xi c I hlowerOne hupperU hlo hhi hAphys m
  constructor
  · intro p c
    have hp : 0 < p.1 := (prime_of_mem_primeBand p.2).pos
    have hraw :=
      B.abs_guardedCell_fullTilt_covariance_valuation_physical_le_of_medium
        xi c I hp hAphys0 hAval0 hlowerOne hupperU hlo hhi hAphys
        (hVexpect p c) hsmall (hmediumCov p c)
    have hnum :
        Ccov + 32 * Real.log U * Aphys * Real.log U * Aval ≤ Cfull := by
      dsimp only [Cfull]
      have hrest : 0 ≤ Cmean + 16 * Aphys * Real.log U * Aval := by
        positivity
      linarith
    have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hnum B.L_pos.le)
      (one_div_nonneg.mpr hpR.le))
  · intro p c c'
    have hp : 0 < p.1 := (prime_of_mem_primeBand p.2).pos
    let epsilon : ℝ := Aphys * Real.log U / B.L
    have hepsilon0 : 0 ≤ epsilon := by
      dsimp only [epsilon]
      exact div_nonneg (mul_nonneg hAphys0 hlogU) B.L_pos.le
    have hraw := B.abs_guardedCell_fullTilt_expect_valuation_sub_other_le
      xi c c' hp hepsilon0 hAval0 hscore (hVexpect p)
      (by simpa only [epsilon] using hsmall) (hmediumPair p c c')
    have hrewrite :
        (Cmean / B.L) * (1 / (p.1 : ℝ)) +
            16 * epsilon * (Aval / (p.1 : ℝ)) =
          ((Cmean + 16 * Aphys * Real.log U * Aval) / B.L) *
            (1 / (p.1 : ℝ)) := by
      dsimp only [epsilon]
      ring
    rw [hrewrite] at hraw
    have hnum : Cmean + 16 * Aphys * Real.log U * Aval ≤ Cfull := by
      dsimp only [Cfull]
      have hrest :
          0 ≤ Ccov + 32 * Real.log U * Aphys * Real.log U * Aval := by
        positivity
      linarith
    have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hnum B.L_pos.le)
      (one_div_nonneg.mpr hpR.le))

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMediumNuisanceInputReduction -/
section


/-!
# Exact reductions for the two medium-law nuisance inputs

The nuisance Schur row in paper Lemma 8.6 uses two arithmetic facts about
the literal medium-prime component laws:

* a Stieltjes bound for `Cov(v_p, log (m / n))` inside one cell; and
* agreement, to reciprocal-logarithmic precision, of `E v_p` in two cells.

This file proves all finite probability, Abel summation, prime-power
summation, and physical-log identifications surrounding those two facts.
It intentionally does **not** replace the remaining arithmetic estimates by
a bundled certificate.  The hypotheses in the two terminal reductions are
the literal moving-prefix estimate and the literal prime-power/tail
estimates which still have to be obtained from the marked-cell theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.Full

noncomputable section

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Subtracting a deterministic constant from the right statistic does not
change covariance.  This is used to pass exactly from `log m` to
`log (m / n)`. -/
theorem covariance_sub_const_right
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) (a : ℝ) :
    mu.covariance F (fun omega ↦ G omega - a) = mu.covariance F G := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (G omega - a)) =
      (∑ omega, mu.mass omega * G omega) -
        a * (∑ omega, mu.mass omega) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * (F omega * (G omega - a))) =
      (∑ omega, mu.mass omega * (F omega * G omega)) -
        a * (∑ omega, mu.mass omega * F omega) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [mu.mass_sum]
  ring























































end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry















end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]



















end FiniteProbability

namespace FiniteLogStieltjes

open Finset Set

variable {Omega : Type*} [Fintype Omega]

/-- The exact finite Stieltjes implication used by the paper: a uniform
bound for every centered cumulative marked mass is charged once against the
total variation of `log`. -/
theorem abs_covariance_log_le_of_centeredPrefix
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {lo hi : ℕ} {E : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hE : 0 ≤ E)
    (hsupport : ∀ omega, lo < value omega ∧ value omega ≤ hi)
    (hprefix : ∀ t ∈ Set.Ioc (lo : ℝ) (hi : ℝ),
      |∑ k ∈ Icc 0 ⌊t⌋₊, centeredFiberMass mu value A k| ≤ E) :
    |mu.covariance A (fun omega ↦ Real.log (value omega : ℝ))| ≤
      (E / (lo : ℝ)) * ((hi : ℝ) - (lo : ℝ)) := by
  have hleft := sum_centeredFiberMass_Icc_lo_eq_zero
    mu value A (fun omega ↦ (hsupport omega).1)
  have hright := sum_centeredFiberMass_Icc_hi_eq_zero
    mu value A (fun omega ↦ (hsupport omega).2)
  have hAbel := abs_sum_log_mul_le_of_prefix_bound
    (centeredFiberMass mu value A) hlo hlohi hE hleft hright hprefix
  rw [sum_log_centeredFiberMass_eq_covariance mu value A hsupport] at hAbel
  exact hAbel

/-- A centered cumulative fiber mass is exactly covariance with the
corresponding prefix indicator.  This identity lets the existing literal
guard-deletion covariance estimate act directly on moving prefixes. -/
theorem sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) (k : ℕ) :
    (∑ j ∈ Icc 0 k, centeredFiberMass mu value A j) =
      mu.covariance A (fun omega ↦ if value omega ≤ k then 1 else 0) := by
  rw [sum_centeredFiberMass_eq]
  unfold FiniteProbability.covariance FiniteProbability.expect
  simp only [Finset.mem_Icc, Nat.zero_le, true_and]
  let EA : ℝ := ∑ eta, mu.mass eta * A eta
  let prefixMass : ℝ :=
    ∑ omega, if value omega ≤ k then mu.mass omega else 0
  let markedMass : ℝ :=
    ∑ omega, if value omega ≤ k then
      mu.mass omega * A omega else 0
  have hleft :
      (∑ omega, if value omega ≤ k then
          mu.mass omega * (A omega - EA) else 0) =
        markedMass - EA * prefixMass := by
    dsimp only [markedMass, prefixMass]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k
    · simp [h]
      ring
    · simp [h]
  have hmarked :
      (∑ omega, mu.mass omega *
        (A omega * if value omega ≤ k then 1 else 0)) =
          markedMass := by
    dsimp only [markedMass]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k <;> simp [h]
  have hprefix :
      (∑ omega, mu.mass omega *
        (if value omega ≤ k then 1 else 0)) = prefixMass := by
    dsimp only [prefixMass]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k <;> simp [h]
  change
    (∑ omega, if value omega ≤ k then
      mu.mass omega * (A omega - EA) else 0) = _
  rw [hleft, hmarked, hprefix]

end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]





end GuardedUniformCell

namespace PrimePowerTail

open Finset

variable {Omega : Type*} [Fintype Omega]



end PrimePowerTail

namespace PaperBridgeFit

open ArithmeticBandGeometry FiniteLogStieltjes

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- Literal specialization of finite Stieltjes summation to one actual
medium-prime bridge component.  The premise is exactly the centered moving
prefix estimate which the marked-cell/PNT argument must supply; the
conclusion is already the paper's physical statistic, not an abstract test
function. -/
theorem abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) (p : ℕ) {E : ℝ}
    (hlo : 0 < B.sampleData.lo c.2) (hE : 0 ≤ E)
    (hprefix : ∀ t ∈ Set.Ioc
        (B.sampleData.lo c.2 : ℝ) (B.sampleData.hi c.2 : ℝ),
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        FiniteLogStieltjes.centeredFiberMass
          (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ))
            (fun m ↦ valuation p (m : ℕ)) k| ≤ E) :
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      (E / (B.sampleData.lo c.2 : ℝ)) *
        ((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) := by
  let mu := B.cellMediumLaw xi c
  let value : B.sampleData.SampleAt c → ℕ := fun m ↦ (m : ℕ)
  let V : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ valuation p (m : ℕ)
  have hsupport : ∀ m : B.sampleData.SampleAt c,
      B.sampleData.lo c.2 < value m ∧
        value m ≤ B.sampleData.hi c.2 := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    exact ⟨by
      simpa only [value, sample, StructuredSampleData.value,
        StructuredSampleData.cellOf] using B.sampleData.lo_lt_value sample,
      by
      simpa only [value, sample, StructuredSampleData.value,
        StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample⟩
  have hlohi : B.sampleData.lo c.2 ≤ B.sampleData.hi c.2 := by
    let m : B.sampleData.SampleAt c :=
      ⟨(B.sampleData.cellFinset c).min' (B.sampleData.cell_nonempty c),
        Finset.min'_mem _ _⟩
    exact (hsupport m).1.le.trans (hsupport m).2
  have hlog := FiniteLogStieltjes.abs_covariance_log_le_of_centeredPrefix
    mu value V hlo hlohi hE hsupport (by
      simpa only [mu, value, V] using hprefix)
  have hnR : (B.sampleData.n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one))
  have hphysicalPoint :
      (fun m : B.sampleData.SampleAt c ↦ B.physicalScore ⟨c, m⟩) =
        fun m ↦ Real.log (value m : ℝ) -
          Real.log (B.sampleData.n : ℝ) := by
    funext m
    have hmR : (value m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hlo.trans (hsupport m).1))
    unfold physicalScore
    change Real.log ((value m : ℝ) / (B.sampleData.n : ℝ)) = _
    rw [Real.log_div hmR hnR]
  rw [hphysicalPoint,
    FiniteProbability.covariance_sub_const_right]
  simpa only [mu, value, V] using hlog

/-- A physical-interval ratio converts the raw Abel bound into the exact
`constant / (p L)` form used by the nuisance Schur row. -/
theorem abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix_rate
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {p : ℕ}
    {Cprefix Kspan Lscale : ℝ}
    (hp : 0 < p) (hCprefix : 0 ≤ Cprefix)
    (hLscale : 0 < Lscale) (hlo : 0 < B.sampleData.lo c.2)
    (hspan :
      ((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) /
          (B.sampleData.lo c.2 : ℝ) ≤ Kspan)
    (hprefix : ∀ t ∈ Set.Ioc
        (B.sampleData.lo c.2 : ℝ) (B.sampleData.hi c.2 : ℝ),
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        FiniteLogStieltjes.centeredFiberMass
          (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ))
            (fun m ↦ valuation p (m : ℕ)) k| ≤
        (Cprefix / Lscale) * (1 / (p : ℝ))) :
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      ((Kspan * Cprefix) / Lscale) * (1 / (p : ℝ)) := by
  have hE : 0 ≤ (Cprefix / Lscale) * (1 / (p : ℝ)) := by
    positivity
  have hraw :=
    B.abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix
      xi c p hlo hE hprefix
  have hloR : (0 : ℝ) < B.sampleData.lo c.2 := by exact_mod_cast hlo
  have hspan0 : 0 ≤
      ((B.sampleData.hi c.2 : ℝ) -
        (B.sampleData.lo c.2 : ℝ)) := by
    have hle : B.sampleData.lo c.2 ≤ B.sampleData.hi c.2 := by
      obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
      have hmCell := (Finset.mem_sdiff.mp hm).1
      exact (StructuredCells.mem_smoothInterval.mp
        (StructuredCells.mem_structuredCell.mp hmCell).1).1.le.trans
          (StructuredCells.mem_smoothInterval.mp
            (StructuredCells.mem_structuredCell.mp hmCell).1).2.1
    exact sub_nonneg.mpr (by exact_mod_cast hle)
  calc
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      (((Cprefix / Lscale) * (1 / (p : ℝ))) /
          (B.sampleData.lo c.2 : ℝ)) *
        ((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) := hraw
    _ = ((Cprefix / Lscale) * (1 / (p : ℝ))) *
        (((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) /
            (B.sampleData.lo c.2 : ℝ)) := by ring
    _ ≤ ((Cprefix / Lscale) * (1 / (p : ℝ))) * Kspan := by
      exact mul_le_mul_of_nonneg_left hspan hE
    _ = ((Kspan * Cprefix) / Lscale) * (1 / (p : ℝ)) := by ring





end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperCanonicalTiltedPrefixRows -/
section


/-!
# Canonical guard-deleted tilted moving-prefix rows

The raw Taylor row is transported through the literal guard deletion and
the exact canonical sample-space reindexing.  After row normalization, the
guard error contains the factor `p * valuationEnvelope`.  Uniformly in the
moving band this is eventually at most `yNat^2`, so it is absorbed by the
already audited squarefree guard error.  The final coefficient therefore
still satisfies the sharp `epsilon(n) * log L(n) -> 0` rate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperCanonicalTiltedPrefixRows

open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry _root_.Erdos390.Full.PaperBridgeFit
open FiniteProbability ValuationScoreDomination ValuationTiltCell
open PaperGuardCensus GuardDeletionSquarefreeProfiles
open GuardSquarefreeErrorRate PaperPrimePowerTailRate
open PaperFixedFiniteRawTiltedPrefixRows

noncomputable section

set_option maxHeartbeats 1600000









theorem physicalSpanMajorant_nonneg (I : PhysicalIntervals) :
    0 ≤ physicalSpanMajorant I := by
  unfold physicalSpanMajorant
  exact Finset.sum_nonneg fun sigma hsigma ↦
    div_nonneg (mul_nonneg (by norm_num)
      ((I.lower_pos sigma).trans (I.lower_lt_upper sigma)).le)
      (I.lower_pos sigma).le

/-- The literal floored physical endpoints have a uniformly bounded
relative span. -/
theorem eventually_physicalBound_relativeSpan_le
    (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop, ∀ sigma : PhysicalSign,
      0 < physicalBound (I.lower sigma) n ∧
      (((physicalBound (I.upper sigma) n : ℝ) -
          (physicalBound (I.lower sigma) n : ℝ)) /
          (physicalBound (I.lower sigma) n : ℝ)) ≤
        physicalSpanMajorant I := by
  rw [Filter.eventually_all]
  intro sigma
  let A := I.lower sigma
  let C := I.upper sigma
  have hA : 0 < A := I.lower_pos sigma
  have hC : 0 < C := hA.trans (I.lower_lt_upper sigma)
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 / A ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (2 / A))
  filter_upwards [hlarge, Filter.eventually_gt_atTop 0] with n hnlarge hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAnTwo : (2 : ℝ) ≤ A * (n : ℝ) := by
    have := (div_le_iff₀ hA).mp hnlarge
    simpa only [mul_comm] using this
  let lo := physicalBound A n
  let hi := physicalBound C n
  have hloFloor : A * (n : ℝ) < (lo : ℝ) + 1 := by
    dsimp only [lo, physicalBound]
    exact Nat.lt_floor_add_one _
  have hloHalf : A * (n : ℝ) / 2 ≤ (lo : ℝ) := by
    nlinarith
  have hloPosR : (0 : ℝ) < lo :=
    (div_pos (mul_pos hA hnR) (by norm_num)).trans_le hloHalf
  have hloPos : 0 < lo := by exact_mod_cast hloPosR
  have hhi : (hi : ℝ) ≤ C * (n : ℝ) := by
    dsimp only [hi, physicalBound]
    exact Nat.floor_le (mul_nonneg hC.le hnR.le)
  have hspan0 : (0 : ℝ) ≤ (lo : ℝ) := hloPosR.le
  have hnum : (hi : ℝ) - (lo : ℝ) ≤ C * (n : ℝ) := by
    linarith
  have hlocal :
      (((hi : ℝ) - (lo : ℝ)) / (lo : ℝ)) ≤ 2 * C / A := by
    have hfirst := div_le_div_of_nonneg_right hnum hloPosR.le
    have hsecond : C * (n : ℝ) / (lo : ℝ) ≤ 2 * C / A := by
      apply (div_le_iff₀ hloPosR).2
      have hCA0 : 0 ≤ 2 * C / A := by positivity
      have hmul := mul_le_mul_of_nonneg_left hloHalf hCA0
      calc
        C * (n : ℝ) ≤ (2 * C / A) * (A * (n : ℝ) / 2) := by
          field_simp [hA.ne']
          norm_num
        _ ≤ (2 * C / A) * (lo : ℝ) := hmul
    exact hfirst.trans hsecond
  refine ⟨hloPos, hlocal.trans ?_⟩
  unfold physicalSpanMajorant
  exact Finset.single_le_sum
    (fun tau htau ↦ div_nonneg
      (mul_nonneg (by norm_num)
        ((I.lower_pos tau).trans (I.lower_lt_upper tau)).le)
      (I.lower_pos tau).le)
    (Finset.mem_univ sigma)

namespace PaperBridgeFit.BridgeData

open _root_.Erdos390.Full.PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]



/-- The canonical physical marked row obtained by exact finite Stieltjes
summation from the preceding all-prefix theorem.  No prefix estimate remains
in the hypotheses. -/
theorem exists_uniform_canonical_cellMediumLaw_physical_valuation_rate_unrestricted
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
            (c : Cell Head),
            |(B.cellMediumLaw xi c).covariance
                (fun m ↦ valuation p.1 (m : ℕ))
                (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
              epsilon B.sampleData.n / (p.1 : ℝ) := by
  obtain ⟨epsilonPrefix, hepsilonPrefix0, hepsilonPrefixRate,
    Nprefix, hprefix⟩ :=
      exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted
        P I Cprom Cbank G W hW hHeadLe Acoef hAcoef
  let Kspan := physicalSpanMajorant I
  let epsilon : ℕ → ℝ := fun n ↦ Kspan * epsilonPrefix n
  have hKspan : 0 ≤ Kspan := physicalSpanMajorant_nonneg I
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact mul_nonneg hKspan (hepsilonPrefix0 n)
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hK : Tendsto (fun _n : ℕ ↦ Kspan) atTop (nhds Kspan) :=
      tendsto_const_nhds
    have hraw := hK.mul hepsilonPrefixRate
    simpa only [epsilon, mul_zero, mul_assoc] using hraw
  obtain ⟨Nspan, hspan⟩ := Filter.eventually_atTop.mp
    (eventually_physicalBound_relativeSpan_le I)
  refine ⟨epsilon, hepsilon0, hepsilonRate, max Nprefix Nspan, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hsep hremaining hcanonical
  have hNprefix : Nprefix ≤ B.sampleData.n := by omega
  have hNspan : Nspan ≤ B.sampleData.n := by omega
  have hprefixN := hprefix B xi hNprefix hBW heta hsep hremaining hcanonical
  intro p c
  have hspanN := hspan B.sampleData.n hNspan c.2
  have hlo : 0 < B.sampleData.lo c.2 := by
    rw [hcanonical]
    simpa only [canonicalSampleData_lo] using hspanN.1
  have hrelative :
      ((B.sampleData.hi c.2 : ℝ) - (B.sampleData.lo c.2 : ℝ)) /
          (B.sampleData.lo c.2 : ℝ) ≤ Kspan := by
    rw [hcanonical]
    simpa only [canonicalSampleData_lo, canonicalSampleData_hi, Kspan]
      using hspanN.2
  have hcentered : ∀ t ∈ Set.Ioc
      (B.sampleData.lo c.2 : ℝ) (B.sampleData.hi c.2 : ℝ),
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        FiniteLogStieltjes.centeredFiberMass
          (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ))
            (fun m ↦ valuation p.1 (m : ℕ)) k| ≤
        (epsilonPrefix B.sampleData.n / (1 : ℝ)) *
          (1 / (p.1 : ℝ)) := by
    intro t ht
    rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    calc
      _ ≤ epsilonPrefix B.sampleData.n / (p.1 : ℝ) :=
        hprefixN p c ⌊t⌋₊
      _ = (epsilonPrefix B.sampleData.n / (1 : ℝ)) *
          (1 / (p.1 : ℝ)) := by ring
  have hraw := B.abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix_rate
    xi c (prime_of_mem_primeBand p.2).pos
    (hepsilonPrefix0 B.sampleData.n) (by norm_num : (0 : ℝ) < 1)
    hlo hrelative hcentered
  calc
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p.1 (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      (Kspan * epsilonPrefix B.sampleData.n) *
        (1 / (p.1 : ℝ)) := by simpa only [div_one, mul_assoc] using hraw
    _ = epsilon B.sampleData.n / (p.1 : ℝ) := by
      dsimp only [epsilon]
      ring

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalTiltedPrefixRows

end

/- Source module: Erdos390.Full.PaperBridgeBaselineL1 -/
section


/-!
# Uniform baseline-to-actual `L¹` control for the paper bridge

The nuisance covariance argument in Lemma 8.4 needs the *actual* tilted
finite law to remain close to the actual finite baseline law throughout a
fixed effective parameter box.  The medium-prime score is not uniformly
small pointwise, so this cannot be proved by a sup-norm estimate alone.

This file proves the needed finite statement from literal arithmetic-cell
data.  A positive cell-density bound gives an `O(sum_{W<p<=y} 1/p / L)`
first absolute moment for the medium valuation score.  The fixed-dimensional
nuisance score contributes `O(1/L)`.  A fixed pointwise score envelope then
converts that first-moment estimate to normalized `L¹` distance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination DivisibilityMomentBounds
open Erdos390.Full.OmittedScoreCell
open Erdos390.Full.PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-! ## Fixed-interval/effective-box specialization -/



/-- A paper-effective ball directly supplies both coefficient bounds used by
the finite `L¹` theorem. -/
theorem effective_bounds_of_paperEffectiveSize
    (xi : B.ParamSpace) {A : ℝ}
    (hbox : B.paperEffectiveSize xi ≤ A) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) ∧
      ‖B.nuisanceParameter xi‖ ≤ A := by
  have hprimeNorm :
      ‖fun p ↦ B.effectivePrimeCoefficient xi p‖ ≤
        B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg (B.nuisanceParameter xi),
      abs_nonneg (xi MomentCoord.slow)]
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤
      B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg
      (fun p ↦ B.effectivePrimeCoefficient xi p),
      abs_nonneg (xi MomentCoord.slow)]
  constructor
  · intro p
    calc
      |B.effectivePrimeCoefficient xi p| ≤
          ‖fun q ↦ B.effectivePrimeCoefficient xi q‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm
            (fun q ↦ B.effectivePrimeCoefficient xi q) p
      _ ≤ B.paperEffectiveSize xi := hprimeNorm
      _ ≤ A := hbox
  · exact hnuisance.trans hbox







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalMarkedNuisanceRows -/
section


/-!
# Canonical marked nuisance rows on the effective ODE ball

The two canonical medium-law inputs are joined here: the Stieltjes physical
row and the pairwise full-valuation component profile.  The residual physical
tilt is inserted explicitly, and the exact finite-mixture decomposition then
produces every nuisance coordinate.  This is the global marked-row statement
used by the selected-mesh Schur argument.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperCanonicalMarkedNuisanceRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability PaperGuardCensus
open PaperCanonicalTiltedPrefixRows
open PaperCanonicalTiltedValuationMeanRows

noncomputable section

set_option maxHeartbeats 2400000

namespace PaperBridgeFit.BridgeData

open PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- After `W` is fixed, every later effective ODE ball has one sharp marked
nuisance rate.  The rate is uniform in the canonical bridge, the point of the
closed ball, every nuisance coordinate, and every moving band prime.  There
is no premise relating the radius of the ball to `log W`. -/
theorem exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals) (U : ℝ)
    (_hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (P h).primes, p ≤ W)
    (a : NNReal) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \
              (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (c : NuisanceCoord B.HeadIndex)
            (p : BandPrime B.sampleData.n B.sampleData.W),
            |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                (fun m ↦ B.nuisanceStatistic m c)
                (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
              epsilon B.sampleData.n * (1 / (p.1 : ℝ)) := by
  let Acoef : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by positivity
  obtain ⟨Aval, hAval0, epsilonMean, hepsilonMean0, hepsilonMeanRate,
      Nmean, hmean⟩ :=
    Erdos390.Full.PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted
      P I Cprom Cbank G W hW hHeadLe Acoef hAcoef
  obtain ⟨epsilonPhysical, hepsilonPhysical0, hepsilonPhysicalRate,
      Nphysical, hphysical⟩ :=
    Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_physical_valuation_rate_unrestricted
      P I Cprom Cbank G W hW hHeadLe Acoef hAcoef
  let structuralConstant : ℝ :=
    32 * Real.log U * Acoef * Real.log U * Aval +
      16 * Acoef * Real.log U * Aval
  let profileError : ℕ → ℝ := fun n ↦
    epsilonPhysical n + epsilonMean n + structuralConstant / L n
  let nuisanceFactor : ℝ := 6 * (1 + 2 * Real.log U)
  let epsilon : ℕ → ℝ := fun n ↦ nuisanceFactor * profileError n
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hlogU0 : 0 ≤ Real.log U := (Real.log_pos hUstrict).le
  have hstructural0 : 0 ≤ structuralConstant := by
    dsimp only [structuralConstant]
    positivity
  have hL0 : ∀ n : ℕ, 0 ≤ L n := by
    intro n
    cases n with
    | zero => norm_num [L]
    | succ n =>
      exact Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hprofile0 : ∀ n, 0 ≤ profileError n := by
    intro n
    dsimp only [profileError]
    exact add_nonneg
      (add_nonneg (hepsilonPhysical0 n) (hepsilonMean0 n))
      (div_nonneg hstructural0 (hL0 n))
  have hnuisanceFactor0 : 0 ≤ nuisanceFactor := by
    dsimp only [nuisanceFactor]
    positivity
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    exact mul_nonneg hnuisanceFactor0 (hprofile0 n)
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLdivL : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hstructuralRate : Tendsto (fun n : ℕ ↦
      (structuralConstant / L n) * Real.log (L n))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ structuralConstant)
        atTop (nhds structuralConstant) := tendsto_const_nhds
    have hmul := hconst.mul hlogLdivL
    have hzero : Tendsto (fun n : ℕ ↦
        structuralConstant * (Real.log (L n) / L n))
        atTop (nhds 0) := by simpa only [mul_zero] using hmul
    apply hzero.congr'
    filter_upwards with n
    ring
  have hprofileRate : Tendsto (fun n : ℕ ↦
      profileError n * Real.log (L n)) atTop (nhds 0) := by
    have hsum :=
      (hepsilonPhysicalRate.add hepsilonMeanRate).add hstructuralRate
    simpa only [profileError, add_mul, zero_add] using hsum
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ nuisanceFactor)
        atTop (nhds nuisanceFactor) := tendsto_const_nhds
    have hmul := hconst.mul hprofileRate
    simpa only [epsilon, mul_zero, mul_assoc] using hmul
  have hsmallT : Tendsto (fun n : ℕ ↦
      8 * (Acoef * Real.log U / L n)) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hLTop
    have hconst : Tendsto (fun _n : ℕ ↦ 8 * (Acoef * Real.log U))
        atTop (nhds (8 * (Acoef * Real.log U))) := tendsto_const_nhds
    have hmul := hconst.mul hinv
    have hzero : Tendsto (fun n : ℕ ↦
        (8 * (Acoef * Real.log U)) * (L n)⁻¹) atTop (nhds 0) := by
      simpa only [mul_zero] using hmul
    apply hzero.congr'
    filter_upwards with n
    rw [div_eq_mul_inv]
    ring
  have hsmallEvent : ∀ᶠ n : ℕ in atTop,
      8 * (Acoef * Real.log U / L n) ≤ 1 :=
    hsmallT.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.mp hsmallEvent
  refine ⟨epsilon, hepsilon0, hepsilonRate,
    max Nmean (max Nphysical Nsmall), ?_⟩
  intro Band _instBand _instBandDec B z hz hN hBW hsep hremaining hcanonical
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hNmean : Nmean ≤ B.sampleData.n := by omega
  have hNphysical : Nphysical ≤ B.sampleData.n := by omega
  have hNsmallBound : Nsmall ≤ B.sampleData.n := by omega
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have hbounds := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef := hbounds.1
  have hnuisanceNorm : ‖B.nuisanceParameter xi‖ ≤ Acoef := hbounds.2
  have hphys : |xi MomentCoord.physical| ≤ Acoef := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ := by
        exact PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Acoef := hnuisanceNorm
  have hmeanN := hmean B xi hNmean hBW heta hsep hremaining hcanonical
  have hphysicalN :=
    hphysical B xi hNphysical hBW heta hsep hremaining hcanonical
  have hsmall : 8 * (Acoef * Real.log U / B.L) ≤ 1 := by
    simpa only [BridgeData.L, Scale.L] using
      hNsmall B.sampleData.n hNsmallBound
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  let Ccov : ℝ := B.L * epsilonPhysical B.sampleData.n
  let Cmean : ℝ := B.L * epsilonMean B.sampleData.n
  have hCcov : 0 ≤ Ccov :=
    mul_nonneg B.L_pos.le (hepsilonPhysical0 B.sampleData.n)
  have hCmean : 0 ≤ Cmean :=
    mul_nonneg B.L_pos.le (hepsilonMean0 B.sampleData.n)
  have hmediumCov : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |(B.cellMediumLaw xi c).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
        (Ccov / B.L) * (1 / (p.1 : ℝ)) := by
    intro p c
    calc
      _ ≤ epsilonPhysical B.sampleData.n / (p.1 : ℝ) :=
        hphysicalN p c
      _ = (Ccov / B.L) * (1 / (p.1 : ℝ)) := by
        dsimp only [Ccov]
        field_simp [B.L_pos.ne']
  have hmediumPair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |(B.cellMediumLaw xi c).expect
            (fun m ↦ valuation p.1 (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
            (fun m ↦ valuation p.1 (m : ℕ))| ≤
        (Cmean / B.L) * (1 / (p.1 : ℝ)) := by
    intro p c c'
    calc
      _ ≤ epsilonMean B.sampleData.n / (p.1 : ℝ) :=
        (hmeanN p).2 c c'
      _ = (Cmean / B.L) * (1 / (p.1 : ℝ)) := by
        dsimp only [Cmean]
        field_simp [B.L_pos.ne']
  have hfullRaw := B.fullTiltCellProfiles_of_medium_stieltjes
    xi I hAcoef hAval0 hCcov hCmean hlowerOne hupperU hlo hhi hphys
    (fun p ↦ (hmeanN p).1) hsmall hmediumCov hmediumPair
  have hfull :
      (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c : Cell Head),
        |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
            (fun m ↦ valuation p.1 (m : ℕ))
            (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
          profileError B.sampleData.n * (1 / (p.1 : ℝ))) ∧
      (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c c' : Cell Head),
        |((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
              (fun m ↦ valuation p.1 (m : ℕ)) -
          ((B.guardedCellProbability c').exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
              (fun m ↦ valuation p.1 (m : ℕ))| ≤
            profileError B.sampleData.n * (1 / (p.1 : ℝ))) := by
    have hrewrite :
        (Ccov + Cmean +
            32 * Real.log U * Acoef * Real.log U * Aval +
            16 * Acoef * Real.log U * Aval) / B.L =
          profileError B.sampleData.n := by
      dsimp only [Ccov, Cmean, profileError]
      rw [show L B.sampleData.n = B.L by rfl]
      dsimp only [structuralConstant]
      field_simp [B.L_pos.ne']
      ring
    simpa only [hrewrite] using hfullRaw
  have hphysicalBound : ∀ m : B.sampleData.Sample,
      |B.physicalScore m| ≤ Real.log U :=
    B.abs_physicalScore_le_log_upperBound I hlowerOne hupperU hlo hhi
  have hmarked :=
    B.nuisanceMarkedRows_le_of_cell_physical_covariance_and_pairwise_valuation
      xi (Cscale := profileError B.sampleData.n) (Lscale := 1)
      (K := Real.log U) (hprofile0 B.sampleData.n) (by norm_num) hlogU0
      hphysicalBound
      (fun p c ↦ by simpa only [div_one] using hfull.1 p c)
      (fun p c c' ↦ by simpa only [div_one] using hfull.2 p c c')
  intro c p
  have hrow := hmarked c p
  simpa only [xi, epsilon, nuisanceFactor, div_one, mul_assoc] using hrow

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalMarkedNuisanceRows

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := by
  exact @Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
