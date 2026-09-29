-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma1_reduction
-- name    : XinGoldbergTBS.Asymptotic.lemma1_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:22:44.314076+00:00
-- url     : https://prove2.me/theorems/cb45119a-e23a-4cf0-91fe-4992637ee37e
-- title:
--   Lemma 1 — $\inf_{\pi\in\Pi}C(\pi)=\inf_{\pi\in\hat\Pi}C(\pi)$
-- statement:
--   (Sheopuri et al. 2010, Lemma 2.1.) For $L > L_0 + 1$,
--   $$\inf_{\pi\in\Pi} C(\pi) = \inf_{\pi\in\hat\Pi} C(\pi),$$
--   where $\hat\Pi \subseteq \Pi$ is the class of policies whose orders in period $t$ are measurable functions of the truncated regular pipeline $\mathcal R^t$ and the expedited inventory position $\hat I_t$ only.
--
--   One may therefore restrict to policies that depend on the $(L - L_0)$-dimensional reduced state. The paper quotes this result from Sheopuri, Janakiraman and Seshadri (2010).
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 440, Lemma 1 (quoted from Sheopuri et al. 2010, Lemma 2.1)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 1 (Sheopuri et al. 2010, Lemma 2.1), p. 440: `inf_{π ∈ Π} C(π) = inf_{π ∈ Π̂} C(π)`. -/
theorem lemma1_reduction (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L) :
    OPT μ κ L₀ L = OPThat μ κ L₀ L := by sorry

end XinGoldbergTBS.Asymptotic
