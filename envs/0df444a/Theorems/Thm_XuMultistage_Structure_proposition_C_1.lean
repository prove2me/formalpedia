-- Prove2me | Theorems.Thm_XuMultistage_Structure_proposition_C_1
-- name    : XuMultistage.Structure.proposition_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:25:18.466304+00:00
-- url     : https://prove2.me/theorems/60805a87-b50f-4554-a88b-9dd631307b59
-- title:
--   Proposition C.1 — optimal path structure for every discount in $[0,1]$
-- statement:
--   Let $N^1=\{1,\ldots,n_1\}$ and $N^2=\{1,\ldots,n_2\}$ be the two finite product catalogs. Prices in each catalog are arbitrary reals in weakly decreasing order, with ties allowed; deterministic utilities are arbitrary reals. Each stage has an always available option $0$ with price and deterministic utility zero. Use the exact two-stage choice probabilities (1), and the undiscounted expected revenue $R_\gamma$ from (2). A feasible binary path matrix satisfies $X_{00}=1$ and $X_{ij}\le X_{i0}$. For an active row, $r_i$ is the conditional total revenue $p_i^{(1)}+\sum_jP_{j\mid i}p_j^{(2)}$, and inactive rows have $r_i=0$.
--
--   For every $0\le\gamma\le1$, there is one globally optimal feasible matrix $X^*$ with all the following properties:
--
--   1. For every ordinary first-stage index $i>0$ and second-stage index $j\ge0$,
--   $$X^*_{ij}=1,\quad 0\le k\le j\quad\Longrightarrow\quad X^*_{ik}=1.$$
--   2. For every $i\ge0$ and $j\ge0$,
--   $$X^*_{ij}=1,\quad 1\le k\le i\quad\Longrightarrow\quad X^*_{kj}=1.$$
--   3. If $\gamma=1$, the same optimizer additionally satisfies
--   $$X^*_{0j}=1,\quad 0\le k\le j\quad\Longrightarrow\quad X^*_{0k}=1.$$
--
--   This is the full structural proposition over the entire closed discount interval. It does not require that row zero be a prefix when $\gamma<1$.
--
--   **Formalization Note** All indices range over their respective finite stage catalogs together with zero. Existence, global optimality, and all three clauses share a single existential witness.
--
--   Differences from the source:
--   - encoding: stage-specific indices 0 through n_t and binary path entries → Fin (n_t + 1) and Boolean entries, with zero reserved for no purchase; reason: the same finite indices and binary feasible choices are represented, including empty assortments and the outside option
--   - encoding: the expected revenue objectives in (2), (5), and (9) → the finite sum of exact first-stage probabilities times conditional total revenues; reason: this equals the path-probability objective on every feasible matrix; at gamma one it is exactly (5), and for positive gamma it is (9)
--   - reading: Appendix C extends (9) to gamma zero although its transformed utilities divide by gamma → the original choice probabilities (1)–(2) also at gamma zero; reason: these are defined at zero and implement the endpoint expressly included on page 38
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), Proposition C.1, PDF/printed p. 38

import Definitions.Def_XuMultistage_Structure_Revenue

namespace XuMultistage.Structure

theorem proposition_C_1 {n₁ n₂ : ℕ} (M : Model n₁ n₂) (horder : M.Ordered)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ X : PathMatrix n₁ n₂, IsOptimal M γ X ∧
      (∀ (i : Fin (n₁ + 1)) (j k : Fin (n₂ + 1)),
        i ≠ 0 → X i j = true → k ≤ j → X i k = true) ∧
      (∀ (i k : Fin (n₁ + 1)) (j : Fin (n₂ + 1)),
        X i j = true → 0 < k → k ≤ i → X k j = true) ∧
      (γ = 1 → ∀ j k : Fin (n₂ + 1), X 0 j = true → k ≤ j → X 0 k = true) := by sorry

end XuMultistage.Structure
