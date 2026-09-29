-- Prove2me | solution 1 for PACBayesInformation.generalization_from_max_description
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:17.308388+00:00
-- url     : https://prove2.me/submissions/e62f8c90-7aed-46ae-adba-d6d2991af1b6

-- Sol generated from MachineLearning/PACBayes/InformationGeneralization.lean
import Mathlib
import Definitions.Def_MachineLearning_PACBayes_InformationGeneralization
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Information-theoretic PAC-Bayes and description length

This file gives a finite, discrete formalization of the bridge from mutual
information to compression-based generalization bounds.  A learner is represented
by the joint law of its training sample and output hypothesis.  Its mutual
information is the expectation of the information density

  log (P(S,H) / (P(S) P(H))).

If a code length dominates this information density pointwise, then mutual
information is at most expected description length.  Consequently every
square-root PAC-Bayes bound expressed using mutual information is bounded by the
corresponding description-length expression.  The final results show that a
uniformly shorter description gives a no-worse generalization guarantee.
-/

open Real BigOperators Finset

noncomputable section

open PACBayesInformation








/-- The basic compression inequality: a pointwise code-length upper bound on
information density bounds mutual information by expected description length. -/
theorem mutualInformation_le_expectedDescriptionLength
    {Sample Hypothesis : Type*} [Fintype Sample] [Fintype Hypothesis]
    (J : JointLaw Sample Hypothesis) (length : Hypothesis → ℝ)
    (hcode : ∀ s h, informationDensity J s h ≤ length h) :
    mutualInformation J ≤ expectedDescriptionLength J length := by
  simp only [mutualInformation, expectedDescriptionLength]
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul_of_nonneg_left (hcode s h) (le_of_lt (J.probability_pos s h))

/-- Replacing mutual information by an expected description-length bound can only
increase the PAC-Bayes radius. -/
theorem informationRadius_le_descriptionRadius
    {Sample Hypothesis : Type*} [Fintype Sample] [Fintype Hypothesis]
    (J : JointLaw Sample Hypothesis) (length : Hypothesis → ℝ)
    (sampleSize : ℕ) (confidencePenalty : ℝ)
    (hsample : 0 < sampleSize)
    (hcode : ∀ s h, informationDensity J s h ≤ length h) :
    generalizationRadius sampleSize (mutualInformation J + confidencePenalty) ≤
      generalizationRadius sampleSize
        (expectedDescriptionLength J length + confidencePenalty) := by
  simp only [generalizationRadius]
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (2 : ℝ) * sampleSize)
  linarith [mutualInformation_le_expectedDescriptionLength J length hcode]

/-- Any information-theoretic PAC-Bayes generalization guarantee transfers to the
corresponding expected-description-length guarantee. -/
theorem generalization_from_expected_description
    {Sample Hypothesis : Type*} [Fintype Sample] [Fintype Hypothesis]
    (J : JointLaw Sample Hypothesis) (length : Hypothesis → ℝ)
    (sampleSize : ℕ) (confidencePenalty gap : ℝ)
    (hsample : 0 < sampleSize)
    (hcode : ∀ s h, informationDensity J s h ≤ length h)
    (hPAC : gap ≤ generalizationRadius sampleSize
      (mutualInformation J + confidencePenalty)) :
    gap ≤ generalizationRadius sampleSize
      (expectedDescriptionLength J length + confidencePenalty) := by
  exact le_trans hPAC (informationRadius_le_descriptionRadius J length sampleSize confidencePenalty hsample hcode)




open PACBayesInformation in
theorem solution    {Sample Hypothesis : Type*} [Fintype Sample] [Fintype Hypothesis]
    (J : JointLaw Sample Hypothesis) (length : Hypothesis → ℝ)
    (sampleSize : ℕ) (confidencePenalty gap maxLength : ℝ)
    (hsample : 0 < sampleSize)
    (hcode : ∀ s h, informationDensity J s h ≤ length h)
    (hlength : ∀ h, length h ≤ maxLength)
    (hPAC : gap ≤ generalizationRadius sampleSize
      (mutualInformation J + confidencePenalty)) :
    gap ≤ generalizationRadius sampleSize (maxLength + confidencePenalty) := by
  -- First, transfer to expected description length bound
  have h1 : gap ≤ generalizationRadius sampleSize (expectedDescriptionLength J length + confidencePenalty) :=
    generalization_from_expected_description J length sampleSize confidencePenalty gap hsample hcode hPAC
  -- Now show expectedDescriptionLength J length ≤ maxLength
  have h2 : expectedDescriptionLength J length ≤ maxLength := by
    simp only [expectedDescriptionLength]
    calc ∑ s, ∑ h, J.probability s h * length h
        ≤ ∑ s, ∑ h, J.probability s h * maxLength := by
          apply Finset.sum_le_sum
          intro s _
          apply Finset.sum_le_sum
          intro h _
          exact mul_le_mul_of_nonneg_left (hlength h) (le_of_lt (J.probability_pos s h))
      _ = maxLength * ∑ s, ∑ h, J.probability s h := by
          rw [Finset.mul_sum _ _ _]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum _ _ _]
          apply Finset.sum_congr rfl
          intro h _
          ring
      _ = maxLength := by rw [J.probability_sum_one, mul_one]
  have h3 : expectedDescriptionLength J length + confidencePenalty ≤ maxLength + confidencePenalty := by linarith [h2]
  exact le_trans h1 (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 * sampleSize)))
