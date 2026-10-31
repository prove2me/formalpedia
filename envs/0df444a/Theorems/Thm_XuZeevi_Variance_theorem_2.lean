-- Prove2me | Theorems.Thm_XuZeevi_Variance_theorem_2
-- name    : XuZeevi.Variance.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:10:23.676909+00:00
-- url     : https://prove2.me/theorems/8e22dded-a54e-46c8-bce2-548a4c26c746
-- title:
--   Theorem 2 — variance-dependent rate for two-stage moment penalization
-- statement:
--   There is one absolute constant $c_1>0$, before and independent of all problem data, with the following property.
--
--   Let $H,Z,P,\ell,h^*,B$ be the bounded measurable learning model, with $n\ge1$, $L_0^*=P\ell(h^*;z)$, $V^*=\operatorname{Var}_P\ell(h^*;z)$, and $F=\ell\circ H-\ell\circ h^*$. Put $C_n=2\log_2n+5$. The primary-sample-dependent surrogate $\psi_S$ satisfies the literal Strategy 2 assumptions on every positive radius, including meaningfulness on the entire nonnegative half-line and measurability of its fixed-radius evaluations and the empirical localization expressions. All probability statements use measurable events; for each measurable function satisfying the claimed threshold graph, the exact risk-bound event is assumed measurable. This regularity convention neither assumes a threshold exists nor asserts a probability bound.
--
--   Assume additionally that $\psi_S(r;\eta)/\sqrt r$ is nonincreasing on $0<r\le4B^2$ for every sample and every fixed $\eta\in(0,1)$, with its zero endpoint expressed by cross multiplication. Let $S,S'$ be independent iid samples of size $n$. On $S'$, choose an exact empirical-risk minimizer and let its measurable attained optimal value be $\widehat L_0^*=\inf_{h\in H}P_{S'}\ell(h;z)$. For each $\delta\in(0,1/2)$ choose any exact minimizer
--   $$\widehat h_{MP}\in\arg\min_h\left\{P_n\ell(h;z)+\psi_S\left(16P_n[(\ell(h;z)-\widehat L_0^*)^2];\delta/C_n\right)\right\}.$$
--   The source asserts a measurable real threshold $r^*(S)$ with the printed fixed-point graph for **$B\psi_S(\cdot;\delta/C_n)$**, and, with probability at least $1-2\delta$ over both samples,
--   $$\mathcal E(\widehat h_{MP})\le\max\left\{2\psi_S(c_1V^*;\delta/C_n),\frac{c_1r^*(S)}{8B}\right\}.$$
--   Neither first-stage accuracy nor a successful first-stage event is assumed. All constants and the factor 16 in the objective are retained. The threshold multiplier is B here and 16B in Theorem 11. Findings I1-I5 are disclosed in the mission: the literal surrogate assumptions are inconsistent and the printed fixed-point graph cannot have a finite real value for a bounded function. This statement is the printed target, not a repaired generalization theorem.
--
--   Differences from the source:
--   - encoding: n independent observations with law P → Fin n indexed sample under the product law, with 0 < n; reason: same joint distribution and normalization; the source divides by n
--   - encoding: arbitrary nonempty class H, measurable bounded losses and a population minimizer → H is the carrier type, hstar is its chosen minimizer, and B > 0 is an envelope; reason: no finiteness or topology is added; any zero-loss model has a positive envelope
--   - encoding: psi may depend on the observed sample → psi takes the primary sample as an argument and is meaningful pointwise, with measurable fixed-radius evaluations and Strategy 2 expressions; reason: retains the sample dependence of pp. 5-6 and empirical localization; the bound need not be uniform across samples
--   - encoding: r* is the fixed point defined on p. 9 → the conclusion asserts a measurable real rstar with IsLUB of {r > 0 : multiplier * psi(r) <= r}, pointwise in the sample; reason: preserves the printed sign and its claimed finite definedness without a junk real supremum; insight I1 records the failure for bounded functions
--   - encoding: p. 5 assumes the relevant suprema and probability events measurable → measurability of the exact displayed event for any measurable function satisfying the printed threshold graph; reason: records only the source regularity convention and does not assume a threshold exists, a deviation estimate, or a probability bound
--   - encoding: with probability at least p → a measurable good event of measure at least ENNReal.ofReal p; reason: equivalent for the measurable events stipulated on p. 5; negative lower bounds impose no probability restriction
--   - encoding: 2n observations split into S and S-prime → two independent Fin n samples under the product of their iid laws; reason: same joint experiment; the first-stage center depends only on the auxiliary sample
--   - encoding: the auxiliary infimum is attained and the second-stage argmin is chosen → arbitrary chosen exact minimizers, with the auxiliary value evaluated at its minimizer; reason: preserves attainment and ties without assuming first-stage accuracy
--   - encoding: sub-root quotient on [0,4B squared] → cross-multiplied inequality for 0 <= r <= t <= 4B squared; reason: equivalent on positive radii and vacuous at r=0 under nonnegativity, avoiding zero division
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Theorem 2, p. 12 (PDF p. 12); https://arxiv.org/abs/2011.06186v4

import Definitions.Def_XuZeevi_Variance_Estimator

open MeasureTheory NatureSLT.Consistency
universe u v

namespace XuZeevi.Variance

theorem theorem_2 : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ {H : Type u} {Z : Type v} [MeasurableSpace Z]
      (P : Measure Z) [IsProbabilityMeasure P]
      (loss : H → Z → ℝ) (hstar : H) (B : ℝ) (n : ℕ), 0 < n →
      IsLearningProblem P loss hstar B →
      ∀ (ψ : (Fin n → Z) → ℝ → ℝ → ℝ), Strategy2Surrogate P loss hstar B ψ →
      (∀ s, SubRootOn B (ψ s)) →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∀ erm : (Fin n → Z) → H, IsAuxiliaryERM loss erm →
      Measurable (auxiliaryValue loss erm) →
      ∀ est : (Fin n → Z) × (Fin n → Z) → H,
      IsMomentEstimator loss ψ δ (auxiliaryValue loss erm) est →
      (∀ t : (Fin n → Z) → ℝ, Measurable t →
        (∀ s, PrintedFixedPoint
          (fun r => B * ψ s r (δ / confidenceDivisor n)) (t s)) →
        MeasurableSet {sa : (Fin n → Z) × (Fin n → Z) | excessRisk P loss hstar (est sa) ≤
          max (2 * ψ sa.1 (c₁ * variance P (loss hstar)) (δ / confidenceDivisor n))
            (c₁ * t sa.1 / (8 * B))}) →
      ∃ rstar : (Fin n → Z) → ℝ, Measurable rstar ∧
        (∀ s, PrintedFixedPoint
          (fun r => B * ψ s r (δ / confidenceDivisor n)) (rstar s)) ∧
        HighProbability (splitLaw P n) (1 - 2 * δ) (fun ss =>
          excessRisk P loss hstar (est ss) ≤
            max (2 * ψ ss.1 (c₁ * variance P (loss hstar)) (δ / confidenceDivisor n))
              (c₁ * rstar ss.1 / (8 * B))) := by sorry

end XuZeevi.Variance
