-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_stationary_witness_exists
-- name    : XinGoldbergTBS.Asymptotic.stationary_witness_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:24:15.793897+00:00
-- url     : https://prove2.me/theorems/28618a0e-9921-4a37-b5db-b9b3b717d713
-- title:
--   Theorem 2 — a stationary-like vector $(\chi^{*,L}, q^{*,L}, \mathcal I^{*,L})$ exists
-- statement:
--   For all $L_0 \ge 0$ and $L > L_0 + 1$, one may construct an $(L - L_0 - 1)$-dimensional random vector $\chi^{*,L}$, an $(L - L_0)$-dimensional random vector $q^{*,L}$, a random variable $\mathcal I^{*,L}$, and i.i.d. demands $\{D_i, i \ge 1\}$ distributed as $D$, on a common probability space, such that properties (i)–(vi) hold:
--
--   (i) nonnegativity of $(\chi^{*,L}, q^{*,L})$ and the independence structure;
--   (ii) $\chi_i^{*,L}\sim\chi_1^{*,L}$ and $q_i^{*,L}\sim q_1^{*,L}$;
--   (iii) the stationarity relation
--   $$\mathcal I^{*,L} + \sum_{i=1}^{k-1}(q_i^{*,L} + \chi_i^{*,L} - D_i) + q_k^{*,L} - \sum_{i=k}^{k+L_0}D_i \sim \mathcal I^{*,L} + q_1^{*,L} - \sum_{i=1}^{L_0+1}D_i,\quad k \in [1, L-L_0];$$
--   (iv) finite means; (v) $\mathbb E[\chi_1^{*,L}] + \mathbb E[q_1^{*,L}] = \mathbb E[D]$;
--   (vi) $$\mathrm{OPT}(L) \ge c(\mathbb E[D] - \mathbb E[\chi_1^{*,L}]) + \mathbb E\Big[G\Big(\mathcal I^{*,L} + q_1^{*,L} - \sum_{i=1}^{L_0+1}D_i\Big)\Big].$$
--
--   This is the core of the lower bound: it produces the vector an optimal stationary policy would have in steady state, without assuming that an optimal or stationary policy exists.
--
--   **Formalization Note** The predicate `IsStationaryWitness` in the definition file spells out (i)–(vi) in full. The probability space is existentially quantified (a type in `Type`).
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 442, Theorem 2

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Theorem 2, p. 442: for all `L₀ ≥ 0` and `L > L₀ + 1` one may construct `χ^{*,L}`, `q^{*,L}`,
`𝓘^{*,L}` and i.i.d. `{D_i, i ≥ 1}` on a common probability space with properties (i)–(vi). -/
theorem stationary_witness_exists (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ),
      IsStationaryWitness P μ κ L₀ L χ q I D := by sorry

end XinGoldbergTBS.Asymptotic
