-- Prove2me | Theorems.Thm_XOSMax_Supplement_lemma_15
-- name    : XOSMax.Supplement.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:37:47.644717+00:00
-- url     : https://prove2.me/theorems/8572452d-0023-455f-9541-50bb750ddd77
-- title:
--   Lemma 15 — Algorithm 5 returns exactly all maximal cliques in $O(n^{k+1})$
-- statement:
--   For every $k\ge2$ there is a constant $C$ such that, for every positive-singleton $k$-XOS representation, the concrete Algorithm 5 program returns exactly the family of inclusion-wise maximal cliques and has charged cost at most
--   $$
--   Cn^{k+1}.
--   $$
--   The program is constructed from the ground enumeration and is not given $k$, the representation, or $f$.
--
--   Differences from the source:
--   - encoding: the family of all inclusion-wise maximal cliques → a finite family whose membership is equivalent to being `cliqueWrt` some clause and not strictly contained in any represented clique; reason: this is exactly inclusion-wise maximality and removes duplicate clauses
--   - encoding: $O(n^{k+1})$ time → oracle calls plus explicitly charged elementary steps bounded by $Cn^{k+1}$, with $C$ chosen after $k$ and before the instance; reason: this is the source's running-time analysis
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 15, pp.9-10

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_cliqueWrt
import Definitions.Def_XOSMax_Supplement_alg5

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Lemma 15.** One deterministic value-oracle algorithm, not given the width, returns exactly all
inclusion-wise maximal cliques of every positive-singleton `k`-XOS representation in
`O(n^(k+1))` time (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3,
Lemma 15, pp.9–10).

**Formalization Note** The program is chosen from the enumeration before `k`, `w`, and `f`.
Membership in its finite output family is equivalent to being a clique not strictly contained in
another clique; duplicate clauses therefore do not create duplicate family members. The cost is the
published charged running time, and its constant may depend on `k` only. -/
theorem lemma_15 :
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℕ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
        L.Nodup → L.toFinset = Finset.univ →
        ∀ (w : Fin k → E → ℝ) (f : Finset E → ℝ),
          Represents w f → (∀ v : E, 0 < f {v}) →
          (∀ X : Finset E, X ∈ (run f (alg5 L)).1 ↔
            ∃ i : Fin k, X = cliqueWrt Finset.univ w f i ∧
              ∀ j : Fin k, ¬ cliqueWrt Finset.univ w f i ⊂ cliqueWrt Finset.univ w f j) ∧
          (run f (alg5 L)).2 ≤ C * Fintype.card E ^ (k + 1) := by sorry

end XOSMax.Supplement
