-- Prove2me | Theorems.Thm_XuMultistage_Structure_lemma_3
-- name    : XuMultistage.Structure.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:25:07.511155+00:00
-- url     : https://prove2.me/theorems/2c8cd082-3041-432b-a75b-3927c842088a
-- title:
--   Lemma 3 — all three path deletion and insertion inequalities
-- statement:
--   Let $N^1=\{1,\ldots,n_1\}$ and $N^2=\{1,\ldots,n_2\}$ be the two finite product catalogs. Prices in each catalog are arbitrary reals in weakly decreasing order, with ties allowed; deterministic utilities are arbitrary reals. Each stage has an always available option $0$ with price and deterministic utility zero. Use the exact two-stage choice probabilities (1), and the undiscounted expected revenue $R_\gamma$ from (2). A feasible binary path matrix satisfies $X_{00}=1$ and $X_{ij}\le X_{i0}$. For an active row, $r_i$ is the conditional total revenue $p_i^{(1)}+\sum_jP_{j\mid i}p_j^{(2)}$, and inactive rows have $r_i=0$.
--
--   Fix $0\le\gamma\le1$ and any feasible $X$, and let $\widetilde p_{ij}=p_i^{(1)}+p_j^{(2)}$. All of the following hold:
--
--   1. If $i,j\ne0$, $X_{ij}=1$, $r_i(X)\ge R_\gamma(X)$, and $\widetilde p_{ij}<\gamma R_\gamma(X)+(1-\gamma)r_i(X)$, then deletion of that path strictly increases revenue:
--   $$R_\gamma(X)<R_\gamma(\operatorname{setPath}(X,i,j,0)).$$
--   2. If $i,j\ne0$, $X_{ij}=0$, $X_{i0}=1$, $r_i(X)\ge R_\gamma(X)$, and $\widetilde p_{ij}\ge\gamma R_\gamma(X)+(1-\gamma)r_i(X)$, then insertion of that path weakly increases revenue:
--   $$R_\gamma(X)\le R_\gamma(\operatorname{setPath}(X,i,j,1)).$$
--   3. If $\gamma=1$, $j\ne0$, $X_{0j}=1$, and $\widetilde p_{0j}<R_\gamma(X)$, deleting that path strictly increases revenue:
--   $$R_\gamma(X)<R_\gamma(\operatorname{setPath}(X,0,j,0)).$$
--
--   These are the three path-modification comparisons in the printed lemma, together in one statement.
--
--   **Formalization Note** Each modification changes exactly one matrix entry. The nonzero column conditions and the active-row condition for insertion ensure that these modifications preserve feasibility. The conditions exclude $(0,0)$ exactly as the source's offered-path set does.
--
--   Differences from the source:
--   - encoding: stage-specific indices 0 through n_t and binary path entries → Fin (n_t + 1) and Boolean entries, with zero reserved for no purchase; reason: the same finite indices and binary feasible choices are represented, including empty assortments and the outside option
--   - encoding: the expected revenue objectives in (2), (5), and (9) → the finite sum of exact first-stage probabilities times conditional total revenues; reason: this equals the path-probability objective on every feasible matrix; at gamma one it is exactly (5), and for positive gamma it is (9)
--   - reading: Appendix C extends (9) to gamma zero although its transformed utilities divide by gamma → the original choice probabilities (1)–(2) also at gamma zero; reason: these are defined at zero and implement the endpoint expressly included on page 38
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), Lemma 3, PDF/printed p. 39

import Definitions.Def_XuMultistage_Structure_Revenue

namespace XuMultistage.Structure

theorem lemma_3 {n₁ n₂ : ℕ} (M : Model n₁ n₂) (horder : M.Ordered)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (X : PathMatrix n₁ n₂) (hfeas : Feasible X) :
    (∀ (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)),
      i ≠ 0 → j ≠ 0 → X i j = true →
      M.pathPrice i j < γ * revenue M γ X + (1 - γ) * conditionalRevenue M X i →
      revenue M γ X ≤ conditionalRevenue M X i →
      revenue M γ X < revenue M γ (setPath X i j false)) ∧
    (∀ (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)),
      i ≠ 0 → j ≠ 0 → X i j = false →
      γ * revenue M γ X + (1 - γ) * conditionalRevenue M X i ≤ M.pathPrice i j →
      revenue M γ X ≤ conditionalRevenue M X i → X i 0 = true →
      revenue M γ X ≤ revenue M γ (setPath X i j true)) ∧
    (γ = 1 → ∀ j : Fin (n₂ + 1), j ≠ 0 → X 0 j = true →
      M.pathPrice 0 j < revenue M γ X →
      revenue M γ X < revenue M γ (setPath X 0 j false)) := by sorry

end XuMultistage.Structure
