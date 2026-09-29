-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_corollary4
-- name    : XinGoldbergTBS.Asymptotic.corollary4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:29:53.243891+00:00
-- url     : https://prove2.me/theorems/3b7612ca-c770-47ec-a9f0-dc42bced77c9
-- title:
--   Corollary 4 — $r_L < \mathbb E[D] - \epsilon_0$ for $L > \epsilon_0^{-2} + L_0 + 1$
-- statement:
--   For all $L > \epsilon_0^{-2} + L_0 + 1$ and every witness of Theorem 2,
--   $$r_L < \mathbb E[D] - \epsilon_0, \qquad r_L = \mathbb E[\chi^{*,L}_1].$$
--
--   The regular order rate of the stationary-like vector stays uniformly bounded away from mean demand, which makes the random-walk bounds of Lemma 5 available with $\epsilon = \epsilon_0$.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 445, Corollary 4

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Corollary 4, p. 445, for every witness of Theorem 2:
if `L > ϵ₀^{-2} + L₀ + 1` then `r_L < 𝔼[D] - ϵ₀`. -/
theorem corollary4 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (hL : (eps0 μ κ L₀ ^ 2)⁻¹ + L₀ + 1 < (L : ℝ)) :
    rL P L₀ L χ < μ.mean - eps0 μ κ L₀ := by sorry

end XinGoldbergTBS.Asymptotic
