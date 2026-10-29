-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_choose_exponents
-- name    : ZhangTangLabelCut.LP2.choose_exponents
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:14:30.400591+00:00
-- url     : https://prove2.me/theorems/adcead7b-4261-4f00-bbe8-b17800f97867
-- title:
--   Lemma 6.5 — exponents giving the nearly cube-root bound
-- statement:
--   For every $0<\epsilon<1/3$, there exist positive real $\delta,\beta$ with $\beta>\delta-1$, a real $C>0$, and an integer $k_0\ge2$, all depending only on $\epsilon$, such that, for every integer $k\ge k_0$,
--   $$k^{1+\delta}\ge Ck\,n(k,\beta,\delta)^{1/3-\epsilon},\qquad n(k,\beta,\delta)=2+(96k^{2\delta}-1)k^\beta k(k-1)/2.$$
--   Here $c=k^{1+\delta}$ and $n$ is the analytic expression for the Section 4 vertex count. This specifies the source's asymptotic parameter choice while retaining the condition needed by Lemma 6.4.
--
--   Differences from the source:
--   - encoding: c = Omega(k n^(1/3-epsilon)) under n = Theta(k²dh) → a positive constant and eventual inequality using the exact real extension of the vertex count; reason: the expression equals n when the parameters are integral and has exactly the source growth rate; integrality is enforced separately for graphs
--   - encoding: appropriate positive beta and delta in the preceding lemma regime → beta > delta - 1 explicitly; reason: the source proof on p. 22 expressly requires equation (20)
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 20, Lemma 6.5; p. 22, equations (25)–(27)

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

namespace ZhangTangLabelCut.LP2

theorem choose_exponents (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 3) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ δ - 1 < β ∧
      ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
        ∀ k : ℕ, k₀ ≤ k →
          C * k * (analyticVertices k β δ) ^ (1 / 3 - ε) ≤ (k : ℝ) ^ (1 + δ) := by sorry

end ZhangTangLabelCut.LP2
