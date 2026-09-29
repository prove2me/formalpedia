-- Prove2me | Theorems.Thm_YogeshwaranDM_hall_iff
-- name    : YogeshwaranDM.hall_iff
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:43:07.784576+00:00
-- url     : https://prove2.me/theorems/0e81691e-030c-4e27-ba77-3c3465c25613
-- title:
--   Theorem 6.2 — Hall's marriage theorem
-- statement:
--   **Theorem 6.2 — Hall's marriage theorem.** Let $G$ be a finite simple bipartite graph with disjoint vertex classes $L,R$ satisfying $V(G)=L\cup R$. For $S\subseteq L$, put $N_G(S)=\bigcup_{x\in S}N_G(x)$. Then
--   $$
--   \bigl(\exists M\subseteq G:\ M\text{ is a complete matching on }L\bigr)
--   \quad\Longleftrightarrow\quad
--   \forall S\subseteq L,\ |S|\le |N_G(S)|.
--   $$
--   Empty vertex classes and the empty subset are allowed.
--
--   **Formalization note.** Graphs and subgraphs are native SimpleGraph objects. The covering equation is explicit because Mathlib's bipartition predicate alone need not cover isolated ambient vertices.
-- source:
--   D. Yogeshwaran, Discrete Mathematics—Lecture Notes, Indian Statistical Institute Bangalore, HTML edition generated May 9, 2025, Theorem 6.2, https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch6.S1.html

import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Tactic
import Definitions.Def_YogeshwaranDM_CompleteMatching

set_option autoImplicit false

namespace YogeshwaranDM

theorem hall_iff {V : Type*} [Fintype V] (G : SimpleGraph V)
    [G.LocallyFinite] (L R : Set V) (hG : G.IsBipartiteWith L R)
    (hcover : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, CompleteMatching M L) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ v ∈ S, G.neighborSet v).ncard := by sorry

end YogeshwaranDM
