-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma4_opt_bound
-- name    : XinGoldbergTBS.Asymptotic.lemma4_opt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:27:16.436261+00:00
-- url     : https://prove2.me/theorems/0d150f13-7dc5-4109-8cb2-d390d9431f51
-- title:
--   Lemma 4 (9) — $\mathrm{OPT}(L) \ge c(\mathbb E[D]-r_L) + (1-\alpha)V^\infty_\alpha(r_L,S^\infty_\alpha(r_L)) - U_0(1-\alpha)^{-3}L\alpha^{L-L_0}$
-- statement:
--   For $L_0 \ge 0$, $L > L_0 + 1$, $\alpha\in(0,1)$, and every witness of Theorem 2 with $r_L = \mathbb E[\chi^{*,L}_1]$:
--   $$\mathrm{OPT}(L) \ge c(\mathbb E[D] - r_L) + (1-\alpha)\,V^\infty_\alpha\big(r_L, S^\infty_\alpha(r_L)\big) - U_0(1-\alpha)^{-3}L\alpha^{L-L_0}. \tag{9}$$
--
--   This replaces the finite-horizon value of Lemma 2 by the infinite-horizon value at its optimal base-stock level, at an explicit cost.
--
--   **Formalization Note** The subtracted term is moved to the left-hand side, $c(\mathbb E[D]-r_L) + (1-\alpha)V^\infty_\alpha(\cdot) \le \mathrm{OPT}(L) + U_0(1-\alpha)^{-3}L\alpha^{L-L_0}$, in $[0,\infty]$; this is equivalent and avoids truncated subtraction.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 444, Lemma 4, Eq. (9)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 4, p. 444, eq. (9), for every witness of Theorem 2:
`OPT(L) ≥ c(𝔼[D] - r_L) + (1 - α) V^∞_α(r_L, S^∞_α(r_L)) - U₀ (1 - α)^{-3} L α^{L-L₀}`
(the subtracted term moved to the left side). -/
theorem lemma4_opt_bound (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          Vinf μ κ L₀ α (rL P L₀ L χ) (Sinf μ κ L₀ α (rL P L₀ L χ))
      ≤ OPT μ κ L₀ L +
        ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) := by sorry

end XinGoldbergTBS.Asymptotic
