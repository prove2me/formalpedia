-- Prove2me | Theorems.Thm_PACBayesInformation_generalization_from_max_description
-- name    : PACBayesInformation.generalization_from_max_description
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:47.002343+00:00
-- url     : https://prove2.me/theorems/615e2eed-975e-48b7-8ebd-a017574c7b06
-- title:
--   If every hypothesis has a description of length at most `maxLength`, the
-- statement:
--   If every hypothesis has a description of length at most `maxLength`, the
--   expected-description result yields a bound using that single maximum length.
--
--   ```lean
--   theorem PACBayesInformation.generalization_from_max_description    {Sample Hypothesis : Type*} [Fintype Sample] [Fintype Hypothesis]
--       (J : JointLaw Sample Hypothesis) (length : Hypothesis → ℝ)
--       (sampleSize : ℕ) (confidencePenalty gap maxLength : ℝ)
--       (hsample : 0 < sampleSize)
--       (hcode : ∀ s h, informationDensity J s h ≤ length h)
--       (hlength : ∀ h, length h ≤ maxLength)
--       (hPAC : gap ≤ generalizationRadius sampleSize
--         (mutualInformation J + confidencePenalty)) :
--       gap ≤ generalizationRadius sampleSize (maxLength + confidencePenalty) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PACBayes/InformationGeneralization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PACBayes/InformationGeneralization.lean#L115

-- Thm stub generated from MachineLearning/PACBayes/InformationGeneralization.lean
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

theorem PACBayesInformation.generalization_from_max_description    {Sample Hypothesis : Type*} [Fintype Sample] [Fintype Hypothesis]
    (J : JointLaw Sample Hypothesis) (length : Hypothesis → ℝ)
    (sampleSize : ℕ) (confidencePenalty gap maxLength : ℝ)
    (hsample : 0 < sampleSize)
    (hcode : ∀ s h, informationDensity J s h ≤ length h)
    (hlength : ∀ h, length h ≤ maxLength)
    (hPAC : gap ≤ generalizationRadius sampleSize
      (mutualInformation J + confidencePenalty)) :
    gap ≤ generalizationRadius sampleSize (maxLength + confidencePenalty) := by sorry
