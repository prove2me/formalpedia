-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:14:21.806883+00:00
-- url     : https://prove2.me/submissions/edc190c5-5199-45f9-a922-cbeb749e7334

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











theorem covariance_smul_left (mu : FiniteProbability Omega)
    (a : ℝ) (F G : Omega → ℝ) :
    mu.covariance (fun omega ↦ a * F omega) G =
      a * mu.covariance F G := by
  unfold covariance
  rw [mu.expect_smul a F]
  rw [show (fun omega ↦ a * F omega * G omega) =
      fun omega ↦ a * (F omega * G omega) by
    funext omega
    ring]
  rw [mu.expect_smul]
  ring









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



theorem smallTiltLoss_nonneg {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 2 * epsilon < 1) :
    0 ≤ smallTiltLoss epsilon := by
  exact div_nonneg (mul_nonneg (by norm_num) hepsilon)
    (sub_nonneg.mpr hsmall.le)

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

/-- Pure covariance algebra: three localized expectation perturbation bounds
give a localized covariance perturbation bound.  The product term is kept at
the product of the two marginal scales. -/
theorem abs_covariance_sub_covariance_le_of_expectation_perturbations
    (mu nu : FiniteProbability Omega) (A B : Omega → ℝ)
    {a b dA dB dAB : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (ha : mu.expect A ≤ a)
    (hb : mu.expect B ≤ b)
    (hdA0 : 0 ≤ dA)
    (hAperturb : |nu.expect A - mu.expect A| ≤ dA)
    (hBperturb : |nu.expect B - mu.expect B| ≤ dB)
    (hABperturb :
      |nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)| ≤ dAB) :
    |nu.covariance A B - mu.covariance A B| ≤
      dAB + (a + dA) * dB + b * dA := by
  have hmuA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hmuB0 : 0 ≤ mu.expect B := mu.expect_nonneg B hB0
  have ha0 : 0 ≤ a := hmuA0.trans ha
  have hb0 : 0 ≤ b := hmuB0.trans hb
  have hnuA : nu.expect A ≤ a + dA := by
    have hle : nu.expect A - mu.expect A ≤ dA :=
      (le_abs_self _).trans hAperturb
    linarith
  have hnuA0 : 0 ≤ nu.expect A := nu.expect_nonneg A hA0
  have hproduct :
      |nu.expect A * nu.expect B - mu.expect A * mu.expect B| ≤
        (a + dA) * dB + b * dA := by
    rw [show nu.expect A * nu.expect B - mu.expect A * mu.expect B =
        nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A) by ring]
    calc
      |nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A)| ≤
          |nu.expect A * (nu.expect B - mu.expect B)| +
            |mu.expect B * (nu.expect A - mu.expect A)| := abs_add_le _ _
      _ = nu.expect A * |nu.expect B - mu.expect B| +
            mu.expect B * |nu.expect A - mu.expect A| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnuA0, abs_of_nonneg hmuB0]
      _ ≤ (a + dA) * dB + b * dA :=
        add_le_add
          (mul_le_mul hnuA hBperturb (abs_nonneg _) (add_nonneg ha0 hdA0))
          (mul_le_mul hb hAperturb (abs_nonneg _) hb0)
  unfold covariance
  rw [show
      (nu.expect (fun omega ↦ A omega * B omega) -
            nu.expect A * nu.expect B) -
          (mu.expect (fun omega ↦ A omega * B omega) -
            mu.expect A * mu.expect B) =
        (nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B) by ring]
  have habs :
      |(nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| :=
    abs_sub _ _
  calc
    |(nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)) -
        (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| := habs
    _ ≤ dAB + ((a + dA) * dB + b * dA) :=
      add_le_add hABperturb hproduct
    _ = dAB + (a + dA) * dB + b * dA := by ring

/-- Localized covariance stability for two `[0,1]`-valued marks under a
pointwise-small exponential tilt. -/
theorem abs_exponentialTilt_covariance_sub_covariance_le_smallTiltLoss
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {epsilon a b c : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 2 * epsilon < 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      let D := smallTiltLoss epsilon
      D * c + (a + D * a) * (D * b) + b * (D * a) := by
  dsimp only
  have hD0 : 0 ≤ smallTiltLoss epsilon :=
    smallTiltLoss_nonneg hepsilon hsmall
  have hAB0 : ∀ omega, 0 ≤ A omega * B omega := fun omega ↦
    mul_nonneg (hA0 omega) (hB0 omega)
  have hAB1 : ∀ omega, A omega * B omega ≤ 1 := by
    intro omega
    exact (mul_le_mul (hA1 omega) (hB1 omega) (hB0 omega) zero_le_one).trans_eq
      (mul_one 1)
  exact abs_covariance_sub_covariance_le_of_expectation_perturbations
    mu (mu.exponentialTilt S) A B hA0 hB0 hAexpect hBexpect
    (mul_nonneg hD0 ((mu.expect_nonneg A hA0).trans hAexpect))
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      A S hA0 hA1 hepsilon hsmall hscore hAexpect)
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      B S hB0 hB1 hepsilon hsmall hscore hBexpect)
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (fun omega ↦ A omega * B omega) S hAB0 hAB1 hepsilon hsmall hscore
      hABexpect)

/-- A simplified product-scale form.  Once the second score is at most
`1/8`, the normalized loss is at most `8 epsilon`, and the quadratic
normalization terms cost only the explicit factor `3 a b`. -/
theorem abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {epsilon a b c : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * epsilon ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      8 * epsilon * (c + 3 * a * b) := by
  have htwo : 2 * epsilon < 1 := by nlinarith
  have hraw :=
    mu.abs_exponentialTilt_covariance_sub_covariance_le_smallTiltLoss
      A B S hA0 hA1 hB0 hB1 hepsilon htwo hscore
      hAexpect hBexpect hABexpect
  let D := smallTiltLoss epsilon
  have hD0 : 0 ≤ D := smallTiltLoss_nonneg hepsilon htwo
  have hD8 : D ≤ 8 * epsilon := smallTiltLoss_le_eight_mul hepsilon hsmall
  have hD1 : D ≤ 1 := hD8.trans hsmall
  have ha0 : 0 ≤ a := (mu.expect_nonneg A hA0).trans hAexpect
  have hb0 : 0 ≤ b := (mu.expect_nonneg B hB0).trans hBexpect
  have hAB0 : ∀ omega, 0 ≤ A omega * B omega := fun omega ↦
    mul_nonneg (hA0 omega) (hB0 omega)
  have hc0 : 0 ≤ c := (mu.expect_nonneg _ hAB0).trans hABexpect
  have hcoef : 2 * D + D ^ 2 ≤ 3 * D := by
    nlinarith [mul_nonneg hD0 (sub_nonneg.mpr hD1)]
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hsum0 : 0 ≤ c + 3 * a * b := by positivity
  refine hraw.trans ?_
  dsimp only
  change
    D * c + (a + D * a) * (D * b) + b * (D * a) ≤
      8 * epsilon * (c + 3 * a * b)
  calc
    D * c + (a + D * a) * (D * b) + b * (D * a) =
        D * c + (2 * D + D ^ 2) * (a * b) := by ring
    _ ≤ D * c + (3 * D) * (a * b) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoef hab0)
    _ = D * (c + 3 * a * b) := by ring
    _ ≤ (8 * epsilon) * (c + 3 * a * b) :=
      mul_le_mul_of_nonneg_right hD8 hsum0

/-- The first mark may be any nonnegative bounded statistic.  Rescaling it
to `[0,1]` introduces no loss in the final expectation-scale bound: the
pointwise bound cancels exactly.  This form is used with an actual valuation
column and a normalized physical logarithm. -/
theorem abs_exponentialTilt_covariance_sub_covariance_le_eight_mul_left_bounded
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {KA epsilon a b c : ℝ}
    (hKA : 0 < KA)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hAKA : ∀ omega, A omega ≤ KA)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * epsilon ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      8 * epsilon * (c + 3 * a * b) := by
  let A' : Omega → ℝ := fun omega ↦ A omega / KA
  have hA'0 : ∀ omega, 0 ≤ A' omega := fun omega ↦
    div_nonneg (hA0 omega) hKA.le
  have hA'1 : ∀ omega, A' omega ≤ 1 := by
    intro omega
    exact (div_le_one hKA).2 (hAKA omega)
  have hA'expect : mu.expect A' ≤ a / KA := by
    have heq : mu.expect A' = (1 / KA) * mu.expect A := by
      rw [show A' = fun omega ↦ (1 / KA) * A omega by
        funext omega
        dsimp only [A']
        ring]
      exact mu.expect_smul (1 / KA) A
    rw [heq]
    calc
      (1 / KA) * mu.expect A = mu.expect A / KA := by ring
      _ ≤ a / KA := div_le_div_of_nonneg_right hAexpect hKA.le
  have hAB'expect :
      mu.expect (fun omega ↦ A' omega * B omega) ≤ c / KA := by
    have heq :
        mu.expect (fun omega ↦ A' omega * B omega) =
          (1 / KA) * mu.expect (fun omega ↦ A omega * B omega) := by
      rw [show (fun omega ↦ A' omega * B omega) =
          fun omega ↦ (1 / KA) * (A omega * B omega) by
        funext omega
        dsimp only [A']
        ring]
      exact mu.expect_smul (1 / KA) (fun omega ↦ A omega * B omega)
    rw [heq]
    calc
      (1 / KA) * mu.expect (fun omega ↦ A omega * B omega) =
          mu.expect (fun omega ↦ A omega * B omega) / KA := by ring
      _ ≤ c / KA := div_le_div_of_nonneg_right hABexpect hKA.le
  have hraw :=
    mu.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
      A' B S hA'0 hA'1 hB0 hB1 hepsilon hsmall hscore
      hA'expect hBexpect hAB'expect
  have hcov (nu : FiniteProbability Omega) :
      nu.covariance A' B = (1 / KA) * nu.covariance A B := by
    rw [show A' = fun omega ↦ (1 / KA) * A omega by
      funext omega
      dsimp only [A']
      ring]
    exact nu.covariance_smul_left (1 / KA) A B
  rw [hcov, hcov] at hraw
  have hdiv :
      |(mu.exponentialTilt S).covariance A B - mu.covariance A B| / KA ≤
        (8 * epsilon * (c + 3 * a * b)) / KA := by
    calc
      |(mu.exponentialTilt S).covariance A B - mu.covariance A B| / KA =
          |((mu.exponentialTilt S).covariance A B -
            mu.covariance A B) / KA| := by
        rw [abs_div, abs_of_pos hKA]
      _ =
          |(1 / KA) * (mu.exponentialTilt S).covariance A B -
            (1 / KA) * mu.covariance A B| := by
        apply congrArg abs
        field_simp [ne_of_gt hKA]
      _ ≤ 8 * epsilon * (c / KA + 3 * (a / KA) * b) := hraw
      _ = (8 * epsilon * (c + 3 * a * b)) / KA := by
        field_simp [ne_of_gt hKA]
  exact (div_le_div_iff_of_pos_right hKA).mp hdiv

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





















/-- The physical residual tilt changes `Cov(v_p,R)` by `O(1/(pL))`, with
all constants explicit.  The hypothesis `hVexpect` is the reciprocal first
moment supplied by the marked-cell estimate for the medium law. -/
theorem abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (I : PhysicalIntervals) {U Aphys Aval : ℝ} {p : ℕ}
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
    (hsmall : 8 * (Aphys * Real.log U / B.L) ≤ 1) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ valuation p (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩) -
        (B.cellMediumLaw xi c).covariance
          (fun m ↦ valuation p (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      32 * Real.log U * (Aphys * Real.log U / B.L) *
        (Aval / (p : ℝ)) := by
  let K : ℝ := Real.log U
  let epsilon : ℝ := Aphys * K / B.L
  let V : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ valuation p (m : ℕ)
  let R : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ B.physicalScore ⟨c, m⟩
  let R' : B.sampleData.SampleAt c → ℝ := fun m ↦ R m / K
  let a : ℝ := Aval / (p : ℝ)
  have hU : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hK : 0 < K := by
    exact Real.log_pos hU
  have hEndpoint : (0 : ℝ) < B.sampleEndpoint := by
    exact_mod_cast B.sampleEndpoint_pos c
  have hV0 : ∀ m, 0 ≤ V m := fun m ↦ valuation_nonneg p (m : ℕ)
  have hVupper : ∀ m, V m ≤ (B.sampleEndpoint : ℝ) :=
    fun m ↦ B.valuation_le_sampleEndpoint c p m
  have hR0 : ∀ m, 0 ≤ R m := by
    intro m
    have hlower := B.log_lower_lt_physicalScore I hlo ⟨c, m⟩
    exact (Real.log_nonneg (hlowerOne c.2)).trans hlower.le
  have hRK : ∀ m, R m ≤ K := by
    intro m
    exact (B.physicalScore_le_log_upper I hhi ⟨c, m⟩).trans
      (Real.log_le_log
        ((I.lower_pos c.2).trans (I.lower_lt_upper c.2))
        (hupperU c.2))
  have hR'0 : ∀ m, 0 ≤ R' m := fun m ↦
    div_nonneg (hR0 m) hK.le
  have hR'1 : ∀ m, R' m ≤ 1 := by
    intro m
    exact (div_le_one hK).2 (hRK m)
  have hepsilon0 : 0 ≤ epsilon := by
    exact div_nonneg (mul_nonneg hAphys0 (Real.log_nonneg hU.le)) B.L_pos.le
  have hscore : ∀ m, |B.cellPhysicalTiltScore xi c m| ≤ epsilon := by
    simpa only [epsilon, K] using
      B.abs_cellPhysicalTiltScore_le_fixedIntervals
        xi c I hlowerOne hupperU hlo hhi hAphys
  have ha0 : 0 ≤ a := div_nonneg hAval0 (by exact_mod_cast hp.le)
  have hVexpect' : (B.cellMediumLaw xi c).expect V ≤ a := by
    simpa only [V, a] using hVexpect
  have hR'expect : (B.cellMediumLaw xi c).expect R' ≤ 1 := by
    calc
      (B.cellMediumLaw xi c).expect R' ≤
          (B.cellMediumLaw xi c).expect (fun _ ↦ (1 : ℝ)) :=
        (B.cellMediumLaw xi c).expect_mono R' _ hR'1
      _ = 1 := by
        unfold FiniteProbability.expect
        rw [← Finset.sum_mul, (B.cellMediumLaw xi c).mass_sum, one_mul]
  have hVR'expect : (B.cellMediumLaw xi c).expect
      (fun m ↦ V m * R' m) ≤ a := by
    calc
      (B.cellMediumLaw xi c).expect (fun m ↦ V m * R' m) ≤
          (B.cellMediumLaw xi c).expect V := by
        apply (B.cellMediumLaw xi c).expect_mono
        intro m
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hR'1 m) (hV0 m)
      _ ≤ a := hVexpect'
  have hraw :=
    FiniteProbability.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul_left_bounded
        (B.cellMediumLaw xi c) V R' (B.cellPhysicalTiltScore xi c)
        hEndpoint hV0 hVupper hR'0 hR'1 hepsilon0
        (by simpa only [epsilon, K] using hsmall) hscore
        hVexpect' hR'expect hVR'expect
  rw [← B.guardedCell_fullTilt_eq_medium_physicalTilt xi c] at hraw
  have hcov (mu : FiniteProbability (B.sampleData.SampleAt c)) :
      mu.covariance V R' = (1 / K) * mu.covariance V R := by
    rw [show R' = fun m ↦ (1 / K) * R m by
      funext m
      dsimp only [R']
      ring]
    exact mu.covariance_smul_right (1 / K) V R
  rw [hcov, hcov] at hraw
  have hdiv :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
          (B.cellMediumLaw xi c).covariance V R| / K ≤
        32 * epsilon * a := by
    calc
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
          (B.cellMediumLaw xi c).covariance V R| / K =
          |(1 / K) *
              ((B.guardedCellProbability c).exponentialTilt
                (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
            (1 / K) * (B.cellMediumLaw xi c).covariance V R| := by
        rw [show |((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
            (B.cellMediumLaw xi c).covariance V R| / K =
          |(((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
            (B.cellMediumLaw xi c).covariance V R) / K| by
              rw [abs_div, abs_of_pos hK]]
        apply congrArg abs
        field_simp [ne_of_gt hK]
      _ ≤ 8 * epsilon * (a + 3 * a * 1) := hraw
      _ = 32 * epsilon * a := by ring
  have hmain :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
          (B.cellMediumLaw xi c).covariance V R| ≤
        32 * K * epsilon * a := by
    have hmul := (div_le_iff₀ hK).mp hdiv
    nlinarith
  simpa only [V, R, epsilon, K, a] using hmain





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
  (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  {U Aphys Aval : Real} {p : Nat},
  LT.lt.{0} (0 : Nat) p →
    LE.le.{0} (0 : Real) Aphys →
      LE.le.{0} (0 : Real) Aval →
        (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
            LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)) →
          (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
              LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) →
            (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                Eq.{1}
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                  (Erdos390.Full.ArithmeticModel.physicalBound
                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))) →
              (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                  Eq.{1}
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                    (Erdos390.Full.ArithmeticModel.physicalBound
                      (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))) →
                LE.le.{0}
                    (abs.{0}
                      (WithLp.ofLp.{max u_1 u_2} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}))
                    Aphys →
                  LE.le.{0}
                      (Erdos390.Full.FiniteProbability.expect.{0}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c) fun m =>
                        Erdos390.Full.ArithmeticModel.valuation p ↑m)
                      (HDiv.hDiv.{0, 0, 0} Aval ↑p) →
                    LE.le.{0}
                        (HMul.hMul.{0, 0, 0} (8 : Real)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys (Real.log U))
                            (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B)))
                        (1 : Real) →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.covariance.{0}
                              (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c)
                                (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c))
                              (fun m => Erdos390.Full.ArithmeticModel.valuation p ↑m) fun m =>
                              Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} B
                                (Sigma.mk.{u_1, 0} c m))
                            (Erdos390.Full.FiniteProbability.covariance.{0}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c)
                              (fun m => Erdos390.Full.ArithmeticModel.valuation p ↑m) fun m =>
                              Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} B
                                (Sigma.mk.{u_1, 0} c m))))
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (32 : Real) (Real.log U))
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys (Real.log U))
                              (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B)))
                          (HDiv.hDiv.{0, 0, 0} Aval ↑p)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
