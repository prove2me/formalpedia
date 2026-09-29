-- Prove2me | Theorems.Thm_YogeshwaranDM_regular_bipartite_perfect_matching
-- name    : YogeshwaranDM.regular_bipartite_perfect_matching
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:43:16.259357+00:00
-- url     : https://prove2.me/theorems/4e1e6de8-c286-4453-a034-b12e4f378aaa
-- title:
--   Exercise 6.3 — Perfect matchings in regular bipartite graphs
-- statement:
--   **Exercise 6.3 — Perfect matchings in regular bipartite graphs.** Let $G$ be a finite simple bipartite graph with disjoint vertex classes $L,R$ covering $V(G)$. Let $k$ be a natural number with $k>0$. If every vertex has degree $k$, then
--   $$
--   \exists M\subseteq G,\qquad M\text{ is a perfect matching of }G.
--   $$
--   No separate nonemptiness assumption is imposed.
--
--   **Formalization note.** The conclusion uses the native IsPerfectMatching predicate. In particular, every ambient vertex is matched; the conclusion is not only a matching on the left class.
-- source:
--   D. Yogeshwaran, Discrete Mathematics—Lecture Notes, Indian Statistical Institute Bangalore, HTML edition generated May 9, 2025, Exercise(A) 6.3, https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch6.S1.html

import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Tactic

set_option autoImplicit false

namespace YogeshwaranDM

theorem regular_bipartite_perfect_matching {V : Type*} [Fintype V]
    (G : SimpleGraph V) [G.LocallyFinite] (L R : Set V)
    (hG : G.IsBipartiteWith L R) (hcover : L ∪ R = Set.univ)
    (k : ℕ) (hk : 0 < k) (hreg : ∀ v, G.degree v = k) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by sorry

end YogeshwaranDM
