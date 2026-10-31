-- Prove2me | Theorems.Thm_XuZeevi_Variance_lemma_3
-- name    : XuZeevi.Variance.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:09:13.711974+00:00
-- url     : https://prove2.me/theorems/d3b3b4cc-11aa-4d12-97a2-2f55f97c2f3a
-- title:
--   Lemma 3 — bound on localized empirical processes
-- statement:
--   In the bounded learning model, let $\psi_S$ satisfy Strategy 2 exactly, including boundedness and the all-radius domination requirement. For a fixed $\delta_1\in(0,1)$ the source asserts a measurable finite threshold $r_1^*(S;\delta_1)$ with the printed fixed-point graph for $16B\psi_S(\cdot;\delta_1)$. On one measurable event of probability at least $1-\delta_1$, simultaneously for every $r>0$,
--   $$\sup_{f\in F:\,Pf^2\le r}(P-P_n)f\le\psi_S\bigl(\max\{r,r_1^*(S;\delta_1)\};\delta_1\bigr).$$
--   The exact all-radius event is assumed measurable whenever its threshold is measurable and satisfies that graph. This assumption asserts no existence or probability estimate. Fixed-point existence is part of the conclusion.
--
--   The finite fixed-point and surrogate defects I1-I2 remain; the printed simultaneous quantifier is retained despite the proof gap I5. This is not a claim of a nonvacuous rate under consistent assumptions.
--
--   Differences from the source:
--   - encoding: n independent observations with law P → Fin n indexed sample under the product law, with 0 < n; reason: same joint distribution and normalization; the source divides by n
--   - encoding: arbitrary nonempty class H, measurable bounded losses and a population minimizer → H is the carrier type, hstar is its chosen minimizer, and B > 0 is an envelope; reason: no finiteness or topology is added; any zero-loss model has a positive envelope
--   - encoding: psi may depend on the observed sample → psi takes the primary sample as an argument and is meaningful pointwise, with measurable fixed-radius evaluations and Strategy 2 expressions; reason: retains the sample dependence of pp. 5-6 and empirical localization; the bound need not be uniform across samples
--   - encoding: r* is the fixed point defined on p. 9 → the conclusion asserts a measurable real rstar with IsLUB of {r > 0 : multiplier * psi(r) <= r}, pointwise in the sample; reason: preserves the printed sign and its claimed finite definedness without a junk real supremum; insight I1 records the failure for bounded functions
--   - encoding: p. 5 assumes the relevant suprema and probability events measurable → measurability of the exact displayed event for any measurable function satisfying the printed threshold graph; reason: records only the source regularity convention and does not assume a threshold exists, a deviation estimate, or a probability bound
--   - encoding: with probability at least p → a measurable good event of measure at least ENNReal.ofReal p; reason: equivalent for the measurable events stipulated on p. 5; negative lower bounds impose no probability restriction
--   - encoding: population-localized supremum bound → a uniform bound for every member with Pf squared at most r; reason: the localized class contains zero and is bounded, so the formulations agree
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Lemma 3, p. 50 (PDF p. 50); https://arxiv.org/abs/2011.06186v4

import Definitions.Def_XuZeevi_Variance_Surrogate

open MeasureTheory

namespace XuZeevi.Variance

theorem lemma_3 {H Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (loss : H → Z → ℝ)
    (hstar : H) (B : ℝ) (n : ℕ) (hn : 0 < n)
    (hmodel : IsLearningProblem P loss hstar B)
    (ψ : (Fin n → Z) → ℝ → ℝ → ℝ)
    (hψ : Strategy2Surrogate P loss hstar B ψ)
    (δ₁ : ℝ) (hδ : 0 < δ₁ ∧ δ₁ < 1)
    (hregular : ∀ t : (Fin n → Z) → ℝ, Measurable t →
      (∀ s, PrintedFixedPoint (fun r => 16 * B * ψ s r δ₁) (t s)) →
      MeasurableSet {s | ∀ r : ℝ, 0 < r →
        ∀ f ∈ excessClass loss hstar, (∫ z, f z ^ 2 ∂P) ≤ r →
          (∫ z, f z ∂P) - empiricalMean s f ≤ ψ s (max r (t s)) δ₁}) :
    ∃ rstar : (Fin n → Z) → ℝ, Measurable rstar ∧
      (∀ s, PrintedFixedPoint (fun r => 16 * B * ψ s r δ₁) (rstar s)) ∧
      HighProbability (sampleLaw P n) (1 - δ₁) (fun s => ∀ r : ℝ, 0 < r →
        ∀ f ∈ excessClass loss hstar, (∫ z, f z ^ 2 ∂P) ≤ r →
          (∫ z, f z ∂P) - empiricalMean s f ≤ ψ s (max r (rstar s)) δ₁) := by sorry

end XuZeevi.Variance
