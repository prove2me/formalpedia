-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_vertex_integrality_gap
-- name    : ZhangTangLabelCut.LP2.vertex_integrality_gap
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:12:43.240542+00:00
-- url     : https://prove2.me/theorems/3de8ea64-a279-4569-bcaf-abca3274865e
-- title:
--   Theorem 5.1 — nearly cube-root gap in the vertex budget
-- statement:
--   For every real $\epsilon>0$, there are a real $C_\epsilon>0$ and an integer $N_0\ge 2$, depending only on $\epsilon$, such that for every integer $N\ge N_0$ and for each of the directed and undirected graph conventions, there exists a finite simple label-cut instance $I$ with distinct connected terminals and $2\le n\le N$, where $n$ is its actual vertex count. Its LP2 optimum is finite and positive, and
--   $$\frac{\operatorname{OPT}(I)}{\operatorname{OPT}_f(\mathrm{LP2}(I))}\ge C_\epsilon N^{1/3-\epsilon}.$$
--   The LP uses real nonnegative weights, sums distinct labels along each simple terminal path, and has no coordinate upper bounds. This asserts the full asymptotic worst-case gap in the vertex budget, including arbitrarily large budgets and every positive epsilon.
--
--   Differences from the source:
--   - encoding: Omega of the worst-case ratio as a function of instance size → one positive constant and threshold followed by a witness for every integer size budget; reason: this is the quantified asymptotic worst-case meaning, with the budget at least the witness size
--   - encoding: undirected construction, with the directed extension in Section 7 → a Boolean orientation quantified over both cases; reason: both source graph orientations are preserved
--   - encoding: connected construction instances and the usual fractional optimum → simple connected witnesses with a finite strictly positive extended-real LP value; reason: rules out undefined ratios; LP2 has an attained finite optimum and connected instances have value at least one
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 13, Theorem 5.1; p. 23, directed extension

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut

namespace ZhangTangLabelCut.LP2

theorem vertex_integrality_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ directed : Bool, ∃ I : LabelCut,
        I.graph.directed = directed ∧ I.Admissible ∧
        2 ≤ Fintype.card I.graph.V ∧ Fintype.card I.graph.V ≤ N ∧
        C * (N : ℝ) ^ (1 / 3 - ε) ≤ I.ratio := by sorry

end ZhangTangLabelCut.LP2
