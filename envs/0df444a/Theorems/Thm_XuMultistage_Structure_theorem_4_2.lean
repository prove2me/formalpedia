-- Prove2me | Theorems.Thm_XuMultistage_Structure_theorem_4_2
-- name    : XuMultistage.Structure.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:25:08.373161+00:00
-- url     : https://prove2.me/theorems/e966d6a8-1b27-41cc-9c26-b5ccc99c552b
-- title:
--   Theorem 4.2 — revenue-ordered and nested optimal assortments
-- statement:
--   Consider two finite catalogs $N^1=\{1,\ldots,n_1\}$ and $N^2=\{1,\ldots,n_2\}$ with arbitrary real deterministic utilities and exogenous real prices weakly decreasing within each stage. Price ties are allowed. Option $0$ is always available at each stage and has price and deterministic utility zero. The seller commits to an initial assortment $S\subseteq N^1$ and a continuation assortment $B_i\subseteq N^2$ for each $i\in S\cup\{0\}$. Empty assortments are permitted, and $B_0$ is freely chosen. The customer uses the two-stage probabilities (1), and the seller maximizes the undiscounted revenue (2).
--
--   When $\gamma=1$, there exists one optimal policy $(S^*,B^*)$ among all such deterministic policies satisfying all three properties:
--
--   1. **Revenue-ordered in the first stage:** $S^*=\{1,\ldots,m\}$ for some $0\le m\le n_1$.
--   2. **Revenue-ordered in the second stage:** for every $i\in S^*\cup\{0\}$, $B_i^*=\{1,\ldots,m_i\}$ for some $0\le m_i\le n_2$.
--   3. **Nested in the second stage:**
--   $$B_1^*\supseteq B_2^*\supseteq\cdots\supseteq B_m^*.$$
--
--   In particular, the three clauses hold simultaneously, with no comparison required between $B_0^*$ and the other continuations. This is an exact existence result for a globally optimal policy.
--
--   **Formalization Note** A policy stores ordinary-product assortments and inserts the two outside options when forming its path matrix. Values of continuations after unavailable first-stage products are ignored. Nesting is expressed as $B_i^*\subseteq B_k^*$ for offered positive indices $k\le i$, equivalent to the displayed chain because $S^*$ is a prefix.
--
--   Differences from the source:
--   - encoding: a deterministic policy with continuations on active histories and a chain of nested assortments → finite sets with irrelevant continuations on inactive rows and pairwise inclusions for offered positive indices; reason: every source policy has such an extension, the objective ignores its inactive entries, and on a prefix the pairwise inclusions are exactly the printed chain
--   - encoding: the expected revenue objectives in (2), (5), and (9) → the finite sum of exact first-stage probabilities times conditional total revenues; reason: this equals the path-probability objective on every feasible matrix; at gamma one it is exactly (5), and for positive gamma it is (9)
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), Theorem 4.2, PDF/printed p. 15

import Definitions.Def_XuMultistage_Structure_Revenue
import Definitions.Def_XuMultistage_Structure_RevenueOrdered

namespace XuMultistage.Structure

theorem theorem_4_2 {n₁ n₂ : ℕ} (M : Model n₁ n₂) (horder : M.Ordered) :
    ∃ π : Policy n₁ n₂, IsOptimalPolicy M 1 π ∧
      RevenueOrdered π.first ∧
      (∀ i : Fin (n₁ + 1), (i = 0 ∨ i ∈ π.first) → RevenueOrdered (π.next i)) ∧
      (∀ i ∈ π.first, ∀ k ∈ π.first, k ≤ i → π.next i ⊆ π.next k) := by sorry

end XuMultistage.Structure
