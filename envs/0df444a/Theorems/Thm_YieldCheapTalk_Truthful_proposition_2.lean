-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_proposition_2
-- name    : YieldCheapTalk.Truthful.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:52.807185+00:00
-- url     : https://prove2.me/theorems/925b86b0-6d3d-4f4d-9d6e-b502972e3737
-- title:
--   Proposition 2, p. 14 — a truth-revealing equilibrium exists iff Σ µ(m|H)a_m ≤ [1 + η(1/θ_H + 1/θ_L − 1)]w ≤ Σ µ(m|L)a_m
-- statement:
--   Consider Lu's cheap-talk game: a supplier of privately known yield type $t \in \{H, L\}$ (mean yields $\theta_H > \theta_L$, common coefficient of variation $\delta$) sends a costless, unverifiable report of her type to a buyer who privately knows the market state $m \in \{H, L\}$ (market potentials $a_H > a_L$, inverse demand $a_m - bx$), and the buyer then orders under the contract $(w, \eta)$. Let $\mu(m\mid t)$ be the probability of state $m$ given type $t$. Under the standing assumptions of the model, a truth-revealing perfect Bayesian equilibrium exists — that is, there are an ordering strategy $Q^*$ and beliefs $\beta$ forming a PBE with the truthful messaging strategy $r(t) = t$ — if and only if
--   $$\sum_{m\in M}\mu(m\mid H)\,a_m \;\le\; \Big[1 + \eta\Big(\frac{1}{\theta_H} + \frac{1}{\theta_L} - 1\Big)\Big] w \;\le\; \sum_{m\in M}\mu(m\mid L)\,a_m . \tag{6}$$
--
--   This is the paper's main existence result: the supplier's yield risk can be credibly communicated by cheap talk exactly when the expected market potential conditional on each type brackets the adjusted wholesale rate. In particular (6) requires the low type to expect a higher market potential than the high type.
--
--   **Formalization Note.** The standing assumptions are those of §3 together with $a_H > a_L$, which the paper assumes from p. 12 on; the equivalence itself does not use $a_H > a_L$. $b > 0$ and $w > 0$ are added; with $w > 0$ the model forces $\theta_L > 0$, so $1/\theta_H$ and $1/\theta_L$ are genuine reciprocals. The equilibrium is the paper's PBE (pp. 8–9) with optimality of the order over all $Q \ge 0$ and beliefs that are probability distributions; the statement is not the equivalence of (5) and (6), which is a step of its proof.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), p. 14, Proposition 2, (6)

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem proposition_2 (M : Model) (hM : M.Standing) :
    (∃ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta) ↔
      (∑ m, M.mu m .H * M.a m ≤ (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ∧
        (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ≤
          ∑ m, M.mu m .L * M.a m) := by sorry
end YieldCheapTalk.Truthful
