-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_eventually_z_lt_one
-- name    : ZhangTangLabelCut.LP2.eventually_z_lt_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:14:29.213694+00:00
-- url     : https://prove2.me/theorems/0ce3a6e6-5fa6-40ae-b484-e4ea2a0c53fa
-- title:
--   Lemma 6.4 — the analytic bound is eventually below one
-- statement:
--   Let $\beta,\delta$ be arbitrary positive real constants satisfying $\beta>\delta-1$. In equation (16), substitute $d=32k^{2\delta}$, $h=k^\beta$ and $a=k^\delta$. There is an integer $k_0\ge2$, depending only on $\beta,\delta$, such that
--   $$z(k,32k^{2\delta},k^\beta,k^\delta)<1\qquad\text{for every integer }k\ge k_0.$$
--   The quantities in this lemma are real analytic expressions. Neither exponent is required to be an integer; no graph with a nonintegral number of chains is postulated.
--
--   Differences from the source:
--   - encoding: large enough integer k in the standing construction notation → an integer threshold k0 ≥ 2 and every integer k ≥ k0; reason: makes eventuality explicit without restricting the universally quantified real exponents
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 20, Lemma 6.4 and equations (16)–(21); pp. 21–22, proof

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

namespace ZhangTangLabelCut.LP2

theorem eventually_z_lt_one (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hgap : δ - 1 < β) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → analyticZ k β δ < 1 := by sorry

end ZhangTangLabelCut.LP2
