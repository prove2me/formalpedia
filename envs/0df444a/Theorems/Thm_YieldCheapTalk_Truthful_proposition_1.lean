-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_proposition_1
-- name    : YieldCheapTalk.Truthful.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:45.7564+00:00
-- url     : https://prove2.me/theorems/9e99d1d9-e82a-4d8d-9951-d065aedb6194
-- title:
--   Proposition 1, (3), p. 10 — under symmetric information the buyer's optimal order is Qʳ(θ, a) = ([a − (1 − η)w]θ − ηw)/(2b(1 + δ²)θ²)
-- statement:
--   Let $b > 0$, $w > 0$ and $0 \le \eta \le 1$. Let $\xi$ be a random yield whose law is a probability measure carried by $[0,1]$, with mean $\theta$ and variance $\delta^2\theta^2$, and let $a$ be a market potential with
--   $$a\theta > \eta w + (1-\eta)w\theta .$$
--   Then the buyer who knows the yield distribution has a unique optimal order quantity over $Q \ge 0$, namely
--   $$Q^r(\theta, a) = \frac{[a - (1-\eta)w]\theta - \eta w}{2b(1+\delta^2)\theta^2},$$
--   and it is strictly positive: $Q^r(\theta, a) > 0$, $\Pi_B(Q) \le \Pi_B(Q^r(\theta, a))$ for all $Q \ge 0$, and equality holds only at $Q = Q^r(\theta, a)$. Here $\Pi_B(Q) = E[\xi Q(a - b\xi Q) - \eta w Q - (1-\eta)w\xi Q]$.
--
--   This is the buyer's symmetric-information benchmark: in a truth-revealing equilibrium the buyer orders $Q^r(\theta_t, a_m)$, so the existence question of Proposition 2 becomes a comparison of these closed forms.
--
--   **Formalization Note.** The paper states the range as $\underline\theta(a) < \theta \le \bar\theta$ with $\underline\theta(a) = \eta w/(a - (1-\eta)w)$ and $\bar\theta = 1/(1+\delta^2)$. The upper bound is a consequence of the yield law (footnote 2), so it is not assumed. The lower bound is stated in the product form $a\theta > \eta w + (1-\eta)w\theta$, which is the §3 assumption; given $\theta > 0$ (forced here by the law and $w > 0$), it is equivalent to $\underline\theta(a) < \theta$ with a positive denominator $a - (1-\eta)w$, which the paper presupposes ("the lower bound ensures a positive order quantity", p. 9). Properties (i) (unimodality in $\theta$) and (ii) (log-submodularity) of Proposition 1 are not part of this statement.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), p. 10, Proposition 1, (3); range θ̲(a), θ̄ defined on p. 9

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem proposition_1 (M : Model) (hb : 0 < M.b) (hw : 0 < M.w)
    (heta : M.eta ∈ Set.Icc (0 : ℝ) 1) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (θ a : ℝ) (hmean : ∫ x, x ∂ν = θ)
    (hvar : ∫ x, (x - θ) ^ 2 ∂ν = M.delta ^ 2 * θ ^ 2)
    (hrange : M.eta * M.w + (1 - M.eta) * M.w * θ < a * θ) :
    0 < M.Qr θ a ∧
      (∀ Q, 0 ≤ Q → M.profitYield ν a Q ≤ M.profitYield ν a (M.Qr θ a)) ∧
      (∀ Q, 0 ≤ Q → M.profitYield ν a Q = M.profitYield ν a (M.Qr θ a) → Q = M.Qr θ a) := by sorry
end YieldCheapTalk.Truthful
