-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_expected_profit_symmetric
-- name    : YieldCheapTalk.Truthful.expected_profit_symmetric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:49.487009+00:00
-- url     : https://prove2.me/theorems/736961f4-fb49-4c9b-9c99-ba74862dacb5
-- title:
--   Proof of Proposition 1, OA p. 2 — under symmetric information Π_B(Q) = aθQ − bθ²(1 + δ²)Q² − ηwQ − (1 − η)wθQ
-- statement:
--   Let $\xi$ be a random yield whose law is a probability measure carried by $[0,1]$, with mean $\theta$ and variance $\delta^2\theta^2$. For a market potential $a$, demand slope $b$ and contract $(w,\eta)$, the buyer's expected profit from ordering $Q$ units when he knows the yield distribution is
--   $$\Pi_B(Q) = E\big[\xi Q(a - b\xi Q) - \eta w Q - (1-\eta)w\xi Q\big] = a\theta Q - b\theta^2(1+\delta^2)Q^2 - \eta w Q - (1-\eta)w\theta Q .$$
--   The identity holds for every real $Q$, $a$, $b$, $\eta$ and $w$.
--
--   It turns the buyer's problem into the maximization of an explicit quadratic in $Q$, which is how the closed form (3) of Proposition 1 is obtained.
--
--   **Formalization Note.** The law is required to be a probability measure carried by $[0,1]$ so that the integrals of $\xi$ and $\xi^2$ are the genuine moments.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), OA p. 2 (PDF 29), Online Appendix B, proof of Proposition 1

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem expected_profit_symmetric (M : Model) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (θ a Q : ℝ) (hmean : ∫ x, x ∂ν = θ)
    (hvar : ∫ x, (x - θ) ^ 2 ∂ν = M.delta ^ 2 * θ ^ 2) :
    M.profitYield ν a Q =
      a * θ * Q - M.b * θ ^ 2 * (1 + M.delta ^ 2) * Q ^ 2 - M.eta * M.w * Q
        - (1 - M.eta) * M.w * θ * Q := by sorry
end YieldCheapTalk.Truthful
