-- Prove2me | Theorems.Thm_XuMultistage_Structure_proposition_4_2
-- name    : XuMultistage.Structure.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:25:10.307699+00:00
-- url     : https://prove2.me/theorems/eea87fcb-922e-4e34-9feb-919b7bd0bb1e
-- title:
--   Proposition 4.2 — both optimal path-matrix closure properties
-- statement:
--   Let $N^1=\{1,\ldots,n_1\}$ and $N^2=\{1,\ldots,n_2\}$ be the two finite product catalogs. Prices in each catalog are arbitrary reals in weakly decreasing order, with ties allowed; deterministic utilities are arbitrary reals. Each stage has an always available option $0$ with price and deterministic utility zero. Use the exact two-stage choice probabilities (1), and the undiscounted expected revenue $R_\gamma$ from (2). A feasible binary path matrix satisfies $X_{00}=1$ and $X_{ij}\le X_{i0}$. For an active row, $r_i$ is the conditional total revenue $p_i^{(1)}+\sum_jP_{j\mid i}p_j^{(2)}$, and inactive rows have $r_i=0$.
--
--   At $\gamma=1$, there is one globally optimal feasible matrix $X^*$ for problem (5) with both closure properties:
--
--   1. For every $i\ge0$ and $j\ge0$,
--   $$X^*_{ij}=1,\quad 0\le k\le j\quad\Longrightarrow\quad X^*_{ik}=1.$$
--   2. For every $i\ge0$ and $j\ge0$,
--   $$X^*_{ij}=1,\quad 1\le k\le i\quad\Longrightarrow\quad X^*_{kj}=1.$$
--
--   The first property includes the continuation after no purchase. The second compares only positive first-stage rows, although its premise permits $i=0$ and its columns include zero.
--
--   **Formalization Note** The single objective used throughout specializes to (5) at discount one, because the path weights are $e^{\mu_i^{(1)}+\mu_j^{(2)}}X_{ij}$.
--
--   Differences from the source:
--   - encoding: stage-specific indices 0 through n_t and binary path entries → Fin (n_t + 1) and Boolean entries, with zero reserved for no purchase; reason: the same finite indices and binary feasible choices are represented, including empty assortments and the outside option
--   - encoding: the expected revenue objectives in (2), (5), and (9) → the finite sum of exact first-stage probabilities times conditional total revenues; reason: this equals the path-probability objective on every feasible matrix; at gamma one it is exactly (5), and for positive gamma it is (9)
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), Proposition 4.2, PDF/printed p. 15

import Definitions.Def_XuMultistage_Structure_Revenue

namespace XuMultistage.Structure

theorem proposition_4_2 {n₁ n₂ : ℕ} (M : Model n₁ n₂) (horder : M.Ordered) :
    ∃ X : PathMatrix n₁ n₂, IsOptimal M 1 X ∧
      (∀ (i : Fin (n₁ + 1)) (j k : Fin (n₂ + 1)),
        X i j = true → k ≤ j → X i k = true) ∧
      (∀ (i k : Fin (n₁ + 1)) (j : Fin (n₂ + 1)),
        X i j = true → 0 < k → k ≤ i → X k j = true) := by sorry

end XuMultistage.Structure
