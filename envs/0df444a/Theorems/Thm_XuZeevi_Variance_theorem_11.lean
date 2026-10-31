-- Prove2me | Theorems.Thm_XuZeevi_Variance_theorem_11
-- name    : XuZeevi.Variance.theorem_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:10:18.409988+00:00
-- url     : https://prove2.me/theorems/514308b6-093c-4b63-b0a0-28b9a3d3de68
-- title:
--   Theorem 11 — variance-dependent rate of the second-stage estimator
-- statement:
--   There is one absolute constant $c_0>0$, independent of all spaces, losses, probability laws, sample sizes, confidence levels and surrogates, with the following property.
--
--   Let $H,Z,P,\ell,h^*,B$ be the bounded measurable learning model, with $n\ge1$, $L_0^*=P\ell(h^*;z)$, $V^*=\operatorname{Var}_P\ell(h^*;z)$, and $F=\ell\circ H-\ell\circ h^*$. Put $C_n=2\log_2n+5$. The primary-sample-dependent surrogate $\psi_S$ satisfies the literal Strategy 2 assumptions on every positive radius, including meaningfulness on the entire nonnegative half-line and measurability of its fixed-radius evaluations and the empirical localization expressions. All probability statements use measurable events; for each measurable function satisfying the claimed threshold graph, the exact risk-bound event is assumed measurable. This regularity convention neither assumes a threshold exists nor asserts a probability bound.
--
--   For any $\delta\in(0,1)$ and any measurable preliminary center $a$ with values in $[-B,B]$, independent of the primary sample, let $\widehat h_{MP}$ be any chosen exact minimizer of
--   $$P_n\ell(h;z)+\psi_S\bigl(16P_n[(\ell(h;z)-a)^2];\delta/C_n\bigr).$$
--   Then there is a measurable real $r^*(S)$ having the printed fixed-point graph for $16B\psi_S(\cdot;\delta/C_n)$, and with probability at least $1-\delta$ over the independent primary and auxiliary data,
--   $$\mathcal E(\widehat h_{MP})\le2\psi_S\left(c_0\max\{V^*,(a-L_0^*)^2,r^*(S)\};\delta/C_n\right).$$
--   A fixed center is included by a one-point auxiliary probability space; an auxiliary estimate is included by its independent probability space. The guarantee is for each chosen center, not one event uniform in all centers. There is no sub-root premise or accuracy premise for the center. The literal source defects I1-I2 persist; this statement does not certify a substantive rate under consistent assumptions.
--
--   Differences from the source:
--   - encoding: n independent observations with law P → Fin n indexed sample under the product law, with 0 < n; reason: same joint distribution and normalization; the source divides by n
--   - encoding: arbitrary nonempty class H, measurable bounded losses and a population minimizer → H is the carrier type, hstar is its chosen minimizer, and B > 0 is an envelope; reason: no finiteness or topology is added; any zero-loss model has a positive envelope
--   - encoding: psi may depend on the observed sample → psi takes the primary sample as an argument and is meaningful pointwise, with measurable fixed-radius evaluations and Strategy 2 expressions; reason: retains the sample dependence of pp. 5-6 and empirical localization; the bound need not be uniform across samples
--   - encoding: r* is the fixed point defined on p. 9 → the conclusion asserts a measurable real rstar with IsLUB of {r > 0 : multiplier * psi(r) <= r}, pointwise in the sample; reason: preserves the printed sign and its claimed finite definedness without a junk real supremum; insight I1 records the failure for bounded functions
--   - encoding: p. 5 assumes the relevant suprema and probability events measurable → measurability of the exact displayed event for any measurable function satisfying the printed threshold graph; reason: records only the source regularity convention and does not assume a threshold exists, a deviation estimate, or a probability bound
--   - encoding: with probability at least p → a measurable good event of measure at least ENNReal.ofReal p; reason: equivalent for the measurable events stipulated on p. 5; negative lower bounds impose no probability restriction
--   - encoding: arbitrary preliminary estimate independent of the primary sample → a measurable center on an arbitrary auxiliary probability space Q, with joint law P^n times Q; reason: covers a fixed center and conditioning on independent auxiliary data with the same distribution
--   - encoding: chosen moment-penalized estimator → any function selecting an exact minimum for each primary and auxiliary input; reason: expresses the printed argmin attainment without selecting an infimum default
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Theorem 11, p. 50 (PDF p. 50); https://arxiv.org/abs/2011.06186v4

import Definitions.Def_XuZeevi_Variance_Estimator

open MeasureTheory NatureSLT.Consistency
universe u v w

namespace XuZeevi.Variance

theorem theorem_11 : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {H : Type u} {Z : Type v} {A : Type w}
      [MeasurableSpace Z] [MeasurableSpace A]
      (P : Measure Z) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
      (loss : H → Z → ℝ) (hstar : H) (B : ℝ) (n : ℕ), 0 < n →
      IsLearningProblem P loss hstar B →
      ∀ (ψ : (Fin n → Z) → ℝ → ℝ → ℝ), Strategy2Surrogate P loss hstar B ψ →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ center : A → ℝ, Measurable center → (∀ a, -B ≤ center a ∧ center a ≤ B) →
      ∀ est : (Fin n → Z) × A → H, IsMomentEstimator loss ψ δ center est →
      (∀ t : (Fin n → Z) → ℝ, Measurable t →
        (∀ s, PrintedFixedPoint
          (fun r => 16 * B * ψ s r (δ / confidenceDivisor n)) (t s)) →
        MeasurableSet {sa : (Fin n → Z) × A | excessRisk P loss hstar (est sa) ≤
          2 * ψ sa.1
            (c₀ * max (max (variance P (loss hstar)) ((center sa.2 - risk P loss hstar) ^ 2))
              (t sa.1)) (δ / confidenceDivisor n)}) →
      ∃ rstar : (Fin n → Z) → ℝ, Measurable rstar ∧
        (∀ s, PrintedFixedPoint
          (fun r => 16 * B * ψ s r (δ / confidenceDivisor n)) (rstar s)) ∧
        HighProbability ((sampleLaw P n).prod Q) (1 - δ) (fun sa =>
          excessRisk P loss hstar (est sa) ≤
            2 * ψ sa.1
              (c₀ * max (max (variance P (loss hstar)) ((center sa.2 - risk P loss hstar) ^ 2))
                (rstar sa.1)) (δ / confidenceDivisor n)) := by sorry

end XuZeevi.Variance
