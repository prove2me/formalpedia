-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_large_integral_optimum
-- name    : ZhangTangLabelCut.LP2.large_integral_optimum
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:14:30.149996+00:00
-- url     : https://prove2.me/theorems/d9acc514-9990-48de-b14b-10f22f8afd0a
-- title:
--   Lemma 5.1 — a realization with large integral optimum
-- statement:
--   For each real $\epsilon>0$ there exist an integer $D>0$, a real $C>0$, and an integer $k_0\ge2$, depending only on $\epsilon$, with the following property. For every integer $k\ge k_0$ and each orientation there is a permutation realization $\hat I$ of the Section 4 construction with $d=32k^{2D}$ and $h=k^D$. It is a simple connected graph with finite positive LP optimum. Writing $n,m$ for its actual vertex and edge counts,
--   $$\operatorname{OPT}(\hat I)\ge Ck n^{1/3-\epsilon},\qquad n\le48k^{2+3D},\qquad m\le64k^{2+3D}.$$
--   This is the large-cut witness needed for the integrality-gap theorem, together with its construction and polynomial size control.
--
--   Differences from the source:
--   - generalization: existence of an appropriate Section 4 realization with the Omega lower bound → the same existence within the integral family delta = beta = D, with explicit polynomial size bounds; reason: choosing integer D ≥ 1/(3epsilon) in the nontrivial range proves the original existential claim and retains every epsilon; these are stronger witness specifications, not restrictions on universal graph inputs
--   - encoding: Omega with a constant depending only on epsilon → D, C and k0 are chosen before k and the realization; reason: makes dependencies uniform
--   - encoding: undirected construction, with the directed extension in Section 7 → a Boolean orientation quantified over both cases; reason: both source graph orientations are preserved
--   - encoding: connected construction instances and the usual fractional optimum → simple connected witnesses with a finite strictly positive extended-real LP value; reason: rules out undefined ratios; LP2 has an attained finite optimum and connected instances have value at least one
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 12, Lemma 5.1; p. 20, restatement; Section 4; p. 23, Section 7

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

namespace ZhangTangLabelCut.LP2

theorem large_integral_optimum (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ directed : Bool,
        ∃ σ : Sample k (32 * k ^ (2 * D)) (k ^ D),
          let I := shutterInstance k (32 * k ^ (2 * D)) (k ^ D) directed σ
          I.Admissible ∧
          C * k * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε) ≤ (I.opt : ℝ) ∧
          Fintype.card I.graph.V ≤ 48 * k ^ (2 + 3 * D) ∧
          Fintype.card I.graph.E ≤ 64 * k ^ (2 + 3 * D) := by sorry

end ZhangTangLabelCut.LP2
