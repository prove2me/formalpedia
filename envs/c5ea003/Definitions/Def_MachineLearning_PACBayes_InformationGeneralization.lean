-- Prove2me | Definitions.Def_MachineLearning_PACBayes_InformationGeneralization
-- name    : MachineLearning_PACBayes_InformationGeneralization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:36.385715+00:00
-- url     : https://prove2.me/theorems/2bc6ee83-9abd-4a7d-b3bc-e55acd10042f
-- title:
--   Aether Catalog definitions — MachineLearning_PACBayes_InformationGeneralization
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PACBayes.InformationGeneralization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PACBayes/InformationGeneralization.lean by skeleton subtraction
import Mathlib
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

namespace PACBayesInformation

/-- A strictly positive joint probability law of a training sample and a learned
hypothesis. Strict positivity keeps the finite information density free of endpoint
conventions. -/
structure JointLaw (Sample Hypothesis : Type*) [Fintype Sample] [Fintype Hypothesis] where
  probability : Sample → Hypothesis → ℝ
  probability_pos : ∀ s h, 0 < probability s h
  probability_sum_one : ∑ s, ∑ h, probability s h = 1

/-- The marginal law of the training sample. -/
def JointLaw.sampleMarginal {Sample Hypothesis : Type*}
    [Fintype Sample] [Fintype Hypothesis] (J : JointLaw Sample Hypothesis)
    (s : Sample) : ℝ :=
  ∑ h, J.probability s h

/-- The marginal law of the learned hypothesis. -/
def JointLaw.hypothesisMarginal {Sample Hypothesis : Type*}
    [Fintype Sample] [Fintype Hypothesis] (J : JointLaw Sample Hypothesis)
    (h : Hypothesis) : ℝ :=
  ∑ s, J.probability s h

/-- Pointwise information density between the training sample and learned hypothesis. -/
def informationDensity {Sample Hypothesis : Type*}
    [Fintype Sample] [Fintype Hypothesis] (J : JointLaw Sample Hypothesis)
    (s : Sample) (h : Hypothesis) : ℝ :=
  Real.log (J.probability s h /
    (J.sampleMarginal s * J.hypothesisMarginal h))

/-- Mutual information `I(S;H)` of the training sample and learned hypothesis. -/
def mutualInformation {Sample Hypothesis : Type*}
    [Fintype Sample] [Fintype Hypothesis] (J : JointLaw Sample Hypothesis) : ℝ :=
  ∑ s, ∑ h, J.probability s h * informationDensity J s h

/-- Expected description length of the hypothesis output by the learner. -/
def expectedDescriptionLength {Sample Hypothesis : Type*}
    [Fintype Sample] [Fintype Hypothesis] (J : JointLaw Sample Hypothesis)
    (length : Hypothesis → ℝ) : ℝ :=
  ∑ s, ∑ h, J.probability s h * length h

/-- The square-root complexity term appearing in information-theoretic PAC-Bayes
bounds. The complexity argument may include both mutual information and a
confidence penalty such as `log (1 / δ)`. -/
def generalizationRadius (sampleSize : ℕ) (complexity : ℝ) : ℝ :=
  Real.sqrt (complexity / (2 * (sampleSize : ℝ)))






end PACBayesInformation


