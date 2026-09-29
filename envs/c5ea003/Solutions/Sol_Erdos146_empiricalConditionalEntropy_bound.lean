-- Prove2me | solution 1 for Erdos146.empiricalConditionalEntropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:11:42.451736+00:00
-- url     : https://prove2.me/submissions/e354e37e-46a8-4667-8af8-d9677643bbd1

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_le_one
import Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_nonneg
import Theorems.Thm_Erdos146_BinaryPairKernel_conditionalEntropy_bound
import Theorems.Thm_Erdos146_binaryEntropy_le_one
import Theorems.Thm_Erdos146_binaryEntropy_nonneg
import Theorems.Thm_Erdos146_binaryEntropy_zero
import Theorems.Thm_Erdos146_withoutReplacementBinaryPairExpectation_error
import Theorems.Thm_Erdos146_withoutReplacementBinaryPairMass_nonneg

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

@[simp] theorem binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  simp [binaryEntropy]

theorem binaryEntropy_scale_le (probability scale : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hscale_zero : 0 ≤ scale)
    (hscale_one : scale ≤ 1) :
    scale * binaryEntropy probability ≤
      binaryEntropy (scale * probability) := by
  have hconcavity := Real.strictConcave_binEntropy.concaveOn.2
    (show probability ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hprobability_zero, hprobability_one⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    hscale_zero (sub_nonneg.mpr hscale_one)
    (show scale + (1 - scale) = 1 by ring)
  have hnatural :
      scale * Real.binEntropy probability ≤
        Real.binEntropy (scale * probability) := by
    simpa [smul_eq_mul] using hconcavity
  unfold binaryEntropy
  calc
    scale * (Real.binEntropy probability / Real.log 2) =
      (scale * Real.binEntropy probability) / Real.log 2 := by ring
    _ ≤ Real.binEntropy (scale * probability) / Real.log 2 :=
      (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

theorem binaryEntropy_subadditive (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y ≤ 1) :
    binaryEntropy (x + y) ≤ binaryEntropy x + binaryEntropy y := by
  by_cases hzero : x + y = 0
  · have hxzero : x = 0 := by linarith
    have hyzero : y = 0 := by linarith
    simp [hxzero, hyzero]
  have hpositive : 0 < x + y :=
    lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hzero)
  have hxscale : 0 ≤ x / (x + y) :=
    div_nonneg hx hpositive.le
  have hyscale : 0 ≤ y / (x + y) :=
    div_nonneg hy hpositive.le
  have hxscale_one : x / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hyscale_one : y / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hxentropy := binaryEntropy_scale_le (x + y) (x / (x + y))
    (add_nonneg hx hy) hsum hxscale hxscale_one
  have hyentropy := binaryEntropy_scale_le (x + y) (y / (x + y))
    (add_nonneg hx hy) hsum hyscale hyscale_one
  have hxidentity : x / (x + y) * (x + y) = x := by
    field_simp [hpositive.ne']
  have hyidentity : y / (x + y) * (x + y) = y := by
    field_simp [hpositive.ne']
  rw [hxidentity] at hxentropy
  rw [hyidentity] at hyentropy
  have hcombined := add_le_add hxentropy hyentropy
  have hleft :
      x / (x + y) * binaryEntropy (x + y) +
          y / (x + y) * binaryEntropy (x + y) =
        binaryEntropy (x + y) := by
    field_simp [hpositive.ne']
  rw [hleft] at hcombined
  exact hcombined

theorem abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (x y : ℝ)
    (hxzero : 0 ≤ x) (hxone : x ≤ 1)
    (hyzero : 0 ≤ y) (hyone : y ≤ 1) :
    |binaryEntropy x - binaryEntropy y| ≤
      binaryEntropy |x - y| := by
  have hordered :
      ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x ≤ y →
        |binaryEntropy x - binaryEntropy y| ≤ binaryEntropy |x - y| := by
    intro a b hazero haone hbzero hbone hab
    have hdifference : 0 ≤ b - a := sub_nonneg.mpr hab
    have hforward :
        binaryEntropy b ≤ binaryEntropy a + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive a (b - a)
        hazero hdifference (by linarith)
      have hargument : a + (b - a) = b := by ring
      rwa [hargument] at h
    have hbackward :
        binaryEntropy a ≤ binaryEntropy b + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive (1 - b) (b - a)
        (sub_nonneg.mpr hbone) hdifference (by linarith)
      have hargument : 1 - b + (b - a) = 1 - a := by ring
      rw [hargument, binaryEntropy_one_sub, binaryEntropy_one_sub] at h
      exact h
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_le]
    have hneg : -(a - b) = b - a := by ring
    rw [hneg]
    constructor <;> linarith
  by_cases hxy : x ≤ y
  · exact hordered x y hxzero hxone hyzero hyone hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := hordered y x hyzero hyone hxzero hxone hyx
    simpa [abs_sub_comm] using h

theorem binaryEntropy_mono_on_half
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyhalf : y ≤ (2 : ℝ)⁻¹) :
    binaryEntropy x ≤ binaryEntropy y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hxhalf : x ≤ (2 : ℝ)⁻¹ := hxy.trans hyhalf
  have hnatural := Real.binEntropy_strictMonoOn.monotoneOn
    (show x ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hx, hxhalf⟩)
    (show y ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hy, hyhalf⟩)
    hxy
  unfold binaryEntropy
  exact (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

end

namespace BinaryPairKernel
section
open Filter Finset SimpleGraph
open scoped Topology

theorem bitDisagreementProbability_mem_Icc (parent : Bool)
    (childProbability : ℝ)
    (hzero : 0 ≤ childProbability) (hone : childProbability ≤ 1) :
    0 ≤ bitDisagreementProbability parent childProbability ∧
      bitDisagreementProbability parent childProbability ≤ 1 := by
  cases parent <;> simp [bitDisagreementProbability] <;> constructor <;>
    linarith

end
end BinaryPairKernel

section
open Filter Finset SimpleGraph
open scoped Topology

theorem withoutReplacementBinaryPairMass_sum
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount) :
    (∑ left : Bool, ∑ right : Bool,
      withoutReplacementBinaryPairMass parentCount oneCount left right) = 1 := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

theorem withoutReplacementBinaryPairExpectation_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right) :
    0 ≤ withoutReplacementBinaryPairExpectation parentCount oneCount f := by
  unfold withoutReplacementBinaryPairExpectation
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (withoutReplacementBinaryPairMass_nonneg
      parentCount oneCount hparents hones left right)
    (hf left right)

theorem withoutReplacementBinaryPairExpectation_le_one
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, f left right ≤ 1) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f ≤ 1 := by
  unfold withoutReplacementBinaryPairExpectation
  calc
    (∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right *
          f left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left (hf left right)
            (withoutReplacementBinaryPairMass_nonneg
              parentCount oneCount hparents hones left right)
    _ = 1 := by
      simpa using
        withoutReplacementBinaryPairMass_sum parentCount oneCount hparents

theorem empiricalChildMarginal_mem_Icc
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel) :
    0 ≤ empiricalChildMarginal parentCount oneCount kernel ∧
      empiricalChildMarginal parentCount oneCount kernel ≤ 1 := by
  constructor
  · exact withoutReplacementBinaryPairExpectation_nonneg
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_nonneg
  · exact withoutReplacementBinaryPairExpectation_le_one
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_le_one

theorem empiricalChildMarginal_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    kernel.childProbability
    (fun left right =>
      ⟨kernel.childProbability_nonneg left right,
        kernel.childProbability_le_one left right⟩)
  rw [← hparameter] at herror
  simpa [empiricalChildMarginal, BinaryPairKernel.childMarginal] using herror

theorem empiricalConditionalEntropy_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalConditionalEntropy parentCount oneCount kernel -
      kernel.conditionalEntropy| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    (fun left right => binaryEntropy (kernel.childProbability left right))
    (fun left right =>
      ⟨binaryEntropy_nonneg
        (kernel.childProbability_nonneg left right)
        (kernel.childProbability_le_one left right),
        binaryEntropy_le_one (kernel.childProbability left right)⟩)
  rw [← hparameter] at herror
  simpa [empiricalConditionalEntropy,
    BinaryPairKernel.conditionalEntropy] using herror

theorem empiricalAverageDisagreement_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalAverageDisagreement parentCount oneCount kernel -
      kernel.averageDisagreement| ≤ 1 / (parentCount : ℝ) := by
  let observable : Bool → Bool → ℝ := fun left right =>
    (BinaryPairKernel.bitDisagreementProbability left
        (kernel.childProbability left right) +
      BinaryPairKernel.bitDisagreementProbability right
        (kernel.childProbability left right)) / 2
  have hobservable (left right : Bool) :
      0 ≤ observable left right ∧ observable left right ≤ 1 := by
    have hleft := BinaryPairKernel.bitDisagreementProbability_mem_Icc left
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    have hright := BinaryPairKernel.bitDisagreementProbability_mem_Icc right
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    dsimp [observable]
    constructor <;> linarith
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones observable hobservable
  rw [← hparameter] at herror
  simpa [empiricalAverageDisagreement,
    BinaryPairKernel.averageDisagreement, observable] using herror

theorem empiricalChildMarginal_entropy_error
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |binaryEntropy (empiricalChildMarginal parentCount oneCount kernel) -
      binaryEntropy kernel.childMarginal| ≤
        binaryEntropy (1 / (parentCount : ℝ)) := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hempirical := empiricalChildMarginal_mem_Icc
    parentCount oneCount hparents_two hones kernel
  have hchild :
      0 ≤ kernel.childMarginal ∧ kernel.childMarginal ≤ 1 :=
    ⟨BinaryPairKernel.childMarginal_nonneg kernel,
      BinaryPairKernel.childMarginal_le_one kernel⟩
  have hcoupling := empiricalChildMarginal_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmodulus := abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (empiricalChildMarginal parentCount oneCount kernel)
    kernel.childMarginal hempirical.1 hempirical.2 hchild.1 hchild.2
  have hparents_real : (4 : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hparents
  have hparents_pos : (0 : ℝ) < (parentCount : ℝ) := by
    linarith
  have hhalf : 1 / (parentCount : ℝ) ≤ (2 : ℝ)⁻¹ := by
    apply (div_le_iff₀ hparents_pos).mpr
    norm_num
    linarith
  have hmonotone := binaryEntropy_mono_on_half
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal|
    (1 / (parentCount : ℝ))
    (abs_nonneg _) hcoupling hhalf
  exact hmodulus.trans hmonotone

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hconditional := empiricalConditionalEntropy_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hdisagreement := empiricalAverageDisagreement_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmarginal := empiricalChildMarginal_entropy_error
    parentCount oneCount hparents hones kernel hparameter
  have hindependent := BinaryPairKernel.conditionalEntropy_bound kernel
  have hconditional_upper :
      empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hconditional).2
    linarith
  have hdisagreement_upper :
      kernel.averageDisagreement ≤
        empiricalAverageDisagreement parentCount oneCount kernel +
          1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hdisagreement).1
    linarith
  have hdisagreement_scaled := mul_le_mul_of_nonneg_left
    hdisagreement_upper logTwo_three_pos.le
  have hmarginal_upper :
      binaryEntropy kernel.childMarginal ≤
        binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) +
          binaryEntropy (1 / (parentCount : ℝ)) := by
    have h := (abs_le.mp hmarginal).1
    linarith
  have herror :
      1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2 =
        empiricalEntropyError parentCount := by
    unfold empiricalEntropyError
    ring
  calc
    empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) :=
      hconditional_upper
    _ ≤ kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        (1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2) := by
      nlinarith
    _ = kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
      rw [herror]
