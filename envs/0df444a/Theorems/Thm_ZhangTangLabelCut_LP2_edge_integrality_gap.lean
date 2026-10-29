-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_edge_integrality_gap
-- name    : ZhangTangLabelCut.LP2.edge_integrality_gap
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:12:50.511986+00:00
-- url     : https://prove2.me/theorems/5b6c4453-6a7c-4c9b-83e8-4e74ee07e2aa
-- title:
--   Theorem 1.1 — nearly cube-root gap in the edge budget
-- statement:
--   For every real $\epsilon>0$, there are a real $C_\epsilon>0$ and an integer $M_0\ge 1$, depending only on $\epsilon$, such that for every integer $M\ge M_0$ and for each of the directed and undirected graph conventions, there exists a finite simple label-cut instance $I$ with distinct connected terminals and $1\le m\le M$, where $m$ is its actual edge count. Its LP2 optimum is finite and positive, and
--   $$\frac{\operatorname{OPT}(I)}{\operatorname{OPT}_f(\mathrm{LP2}(I))}\ge C_\epsilon M^{1/3-\epsilon}.$$
--   The LP uses real nonnegative weights, sums distinct labels along each simple terminal path, and has no coordinate upper bounds. This asserts the full asymptotic worst-case gap in the edge budget, including arbitrarily large budgets and every positive epsilon.
--
--   Differences from the source:
--   - encoding: Omega of the worst-case ratio as a function of instance size → one positive constant and threshold followed by a witness for every integer size budget; reason: this is the quantified asymptotic worst-case meaning, with the budget at least the witness size
--   - encoding: undirected construction, with the directed extension in Section 7 → a Boolean orientation quantified over both cases; reason: both source graph orientations are preserved
--   - encoding: connected construction instances and the usual fractional optimum → simple connected witnesses with a finite strictly positive extended-real LP value; reason: rules out undefined ratios; LP2 has an attained finite optimum and connected instances have value at least one
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 4, Theorem 1.1; p. 13, restatement; p. 23, directed extension

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut

namespace ZhangTangLabelCut.LP2

theorem edge_integrality_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, 1 ≤ M₀ ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ directed : Bool, ∃ I : LabelCut,
        I.graph.directed = directed ∧ I.Admissible ∧
        1 ≤ Fintype.card I.graph.E ∧ Fintype.card I.graph.E ≤ M ∧
        C * (M : ℝ) ^ (1 / 3 - ε) ≤ I.ratio := by sorry

end ZhangTangLabelCut.LP2
