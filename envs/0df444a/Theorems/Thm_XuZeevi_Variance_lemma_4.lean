-- Prove2me | Theorems.Thm_XuZeevi_Variance_lemma_4
-- name    : XuZeevi.Variance.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:09:37.092647+00:00
-- url     : https://prove2.me/theorems/33b03dd7-da0b-471f-aa5f-1592cc16152b
-- title:
--   Lemma 4 — uniform convergence with empirical localization
-- statement:
--   In the same bounded learning model and literal Strategy 2 assumptions, fix $\delta_1\in(0,1)$. The source asserts a measurable finite positive $r_1^*(S;\delta_1)$ with the printed fixed-point graph of $16B\psi_S(\cdot;\delta_1)$. There is one measurable event $E$ such that every $S\in E$ and $f\in F$ satisfy
--   $$Pf^2\le r_1^*(S;\delta_1)\quad\text{or}\quad(P-P_n)f\le\psi_S(4P_nf^2;\delta_1).$$
--   Its probability has the printed lower bound
--   $$P^n(E)\ge1-\left(\log_2\frac{\max\{8B^2,2r_1^*(S;\delta_1)\}}{r_1^*(S;\delta_1)}+\frac12\right)\delta_1.$$
--   For a random threshold, the displayed scalar-versus-random inequality is read pointwise for every $S$, with the same event $E$. No expectation or worst-case replacement is inserted. For deterministic surrogates this is precisely the scalar probability bound on the page. The source's exact uniform event is assumed measurable for any measurable threshold satisfying the graph; no probability estimate is assumed.
--
--   Positivity, which the proof claims on p. 52, remains a conclusion. Findings I1-I2 are retained, so the literal assumption class is empty. The logarithm never silently uses a zero denominator.
--
--   Differences from the source:
--   - encoding: n independent observations with law P → Fin n indexed sample under the product law, with 0 < n; reason: same joint distribution and normalization; the source divides by n
--   - encoding: arbitrary nonempty class H, measurable bounded losses and a population minimizer → H is the carrier type, hstar is its chosen minimizer, and B > 0 is an envelope; reason: no finiteness or topology is added; any zero-loss model has a positive envelope
--   - encoding: psi may depend on the observed sample → psi takes the primary sample as an argument and is meaningful pointwise, with measurable fixed-radius evaluations and Strategy 2 expressions; reason: retains the sample dependence of pp. 5-6 and empirical localization; the bound need not be uniform across samples
--   - encoding: r* is the fixed point defined on p. 9 → the conclusion asserts a measurable real rstar with IsLUB of {r > 0 : multiplier * psi(r) <= r}, pointwise in the sample; reason: preserves the printed sign and its claimed finite definedness without a junk real supremum; insight I1 records the failure for bounded functions
--   - encoding: p. 5 assumes the relevant suprema and probability events measurable → measurability of the exact displayed event for any measurable function satisfying the printed threshold graph; reason: records only the source regularity convention and does not assume a threshold exists, a deviation estimate, or a probability bound
--   - encoding: with probability at least p → a measurable good event of measure at least ENNReal.ofReal p; reason: equivalent for the measurable events stipulated on p. 5; negative lower bounds impose no probability restriction
--   - reading: the probability lower bound contains a possibly sample-dependent fixed point without specifying a comparison convention → the same event probability dominates the printed expression for every sample; reason: pointwise reading keeps the displayed inequality and does not average it or impose deterministic surrogates
--   - encoding: the proof claims r1* > 0 before using the ratio → positivity is asserted in the conclusion alongside the fixed-point graph; reason: preserves the source claimed definedness instead of assuming a lemma or using division by zero
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Lemma 4, p. 52 (PDF p. 52); https://arxiv.org/abs/2011.06186v4

import Definitions.Def_XuZeevi_Variance_Surrogate

open MeasureTheory

namespace XuZeevi.Variance

theorem lemma_4 {H Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (loss : H → Z → ℝ)
    (hstar : H) (B : ℝ) (n : ℕ) (hn : 0 < n)
    (hmodel : IsLearningProblem P loss hstar B)
    (ψ : (Fin n → Z) → ℝ → ℝ → ℝ)
    (hψ : Strategy2Surrogate P loss hstar B ψ)
    (δ₁ : ℝ) (hδ : 0 < δ₁ ∧ δ₁ < 1)
    (hregular : ∀ t : (Fin n → Z) → ℝ, Measurable t →
      (∀ s, PrintedFixedPoint (fun r => 16 * B * ψ s r δ₁) (t s)) →
      MeasurableSet {s | ∀ f ∈ excessClass loss hstar,
        (∫ z, f z ^ 2 ∂P) ≤ t s ∨
        (∫ z, f z ∂P) - empiricalMean s f ≤
          ψ s (4 * empiricalMean s (fun z => f z ^ 2)) δ₁}) :
    ∃ rstar : (Fin n → Z) → ℝ, Measurable rstar ∧
      (∀ s, 0 < rstar s ∧ PrintedFixedPoint (fun r => 16 * B * ψ s r δ₁) (rstar s)) ∧
      ∃ E : Set (Fin n → Z), MeasurableSet E ∧
        (∀ s, ENNReal.ofReal (1 -
          (Real.log (max (8 * B ^ 2) (2 * rstar s) / rstar s) / Real.log 2 + 1 / 2) * δ₁)
            ≤ sampleLaw P n E) ∧
        ∀ s ∈ E, ∀ f ∈ excessClass loss hstar,
          (∫ z, f z ^ 2 ∂P) ≤ rstar s ∨
          (∫ z, f z ∂P) - empiricalMean s f ≤
            ψ s (4 * empiricalMean s (fun z => f z ^ 2)) δ₁ := by sorry

end XuZeevi.Variance
