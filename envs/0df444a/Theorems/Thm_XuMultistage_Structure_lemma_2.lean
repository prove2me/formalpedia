-- Prove2me | Theorems.Thm_XuMultistage_Structure_lemma_2
-- name    : XuMultistage.Structure.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:25:03.784013+00:00
-- url     : https://prove2.me/theorems/6e78c2fe-b4ea-4427-851c-24ebc1c0a4ca
-- title:
--   Lemma 2 — active-row conditional revenue dominates optimal revenue
-- statement:
--   Let $N^1=\{1,\ldots,n_1\}$ and $N^2=\{1,\ldots,n_2\}$ be the two finite product catalogs. Prices in each catalog are arbitrary reals in weakly decreasing order, with ties allowed; deterministic utilities are arbitrary reals. Each stage has an always available option $0$ with price and deterministic utility zero. Use the exact two-stage choice probabilities (1), and the undiscounted expected revenue $R_\gamma$ from (2). A feasible binary path matrix satisfies $X_{00}=1$ and $X_{ij}\le X_{i0}$. For an active row, $r_i$ is the conditional total revenue $p_i^{(1)}+\sum_jP_{j\mid i}p_j^{(2)}$, and inactive rows have $r_i=0$.
--
--   Fix $0\le\gamma\le1$. If $X^*$ is globally optimal among all feasible matrices, then every active ordinary first-stage row satisfies
--   $$i\in N^1,\quad X^*_{i0}=1\quad\Longrightarrow\quad r_i(X^*)\ge R_\gamma(X^*).$$
--
--   This is the conditional-revenue comparison for positive first-stage purchases; it asserts no such comparison for row zero.
--
--   **Formalization Note** Global optimality includes feasibility and comparison against all feasible matrices. No structured optimum is assumed.
--
--   Differences from the source:
--   - encoding: stage-specific indices 0 through n_t and binary path entries → Fin (n_t + 1) and Boolean entries, with zero reserved for no purchase; reason: the same finite indices and binary feasible choices are represented, including empty assortments and the outside option
--   - encoding: the expected revenue objectives in (2), (5), and (9) → the finite sum of exact first-stage probabilities times conditional total revenues; reason: this equals the path-probability objective on every feasible matrix; at gamma one it is exactly (5), and for positive gamma it is (9)
--   - reading: Appendix C extends (9) to gamma zero although its transformed utilities divide by gamma → the original choice probabilities (1)–(2) also at gamma zero; reason: these are defined at zero and implement the endpoint expressly included on page 38
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), Lemma 2, PDF/printed p. 39

import Definitions.Def_XuMultistage_Structure_Revenue

namespace XuMultistage.Structure

theorem lemma_2 {n₁ n₂ : ℕ} (M : Model n₁ n₂) (horder : M.Ordered)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (X : PathMatrix n₁ n₂) (hopt : IsOptimal M γ X)
    (i : Fin (n₁ + 1)) (hi : i ≠ 0) (hactive : X i 0 = true) :
    revenue M γ X ≤ conditionalRevenue M X i := by sorry

end XuMultistage.Structure
