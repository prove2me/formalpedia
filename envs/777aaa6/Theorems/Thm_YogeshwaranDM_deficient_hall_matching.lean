-- Prove2me | Theorems.Thm_YogeshwaranDM_deficient_hall_matching
-- name    : YogeshwaranDM.deficient_hall_matching
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:43:26.987145+00:00
-- url     : https://prove2.me/theorems/ebe7e95c-5af4-4cd9-9cd6-2af4d53dcd3b
-- title:
--   Proposition 6.4 — Hall's theorem with a bounded deficit
-- statement:
--   **Proposition 6.4 — Hall's theorem with a bounded deficit.** Let $G$ be a finite simple bipartite graph with vertex partition $L\sqcup R$, and let $d\in\mathbb N$ satisfy $d\ge1$. Suppose
--   $$
--   \forall S\subseteq L,\qquad |N_G(S)|\ge |S|-d.
--   $$
--   Then $G$ contains a matching $M$ for which
--   $$
--   |E(M)|\ge |L|-d.
--   $$
--
--   **Formalization note.** Quantification over finite subsets of the finite subtype $L$ covers every left subset. Natural subtraction is truncated at zero, which is equivalent here to the integer lower bound because edge and neighborhood cardinalities are nonnegative. The conclusion counts actual unordered edges of a native matching subgraph.
-- source:
--   D. Yogeshwaran, Discrete Mathematics—Lecture Notes, Indian Statistical Institute Bangalore, HTML edition generated May 9, 2025, Proposition 6.4, https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch6.S1.html

import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

set_option autoImplicit false

namespace YogeshwaranDM

theorem deficient_hall_matching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (L R : Set V)
    (hG : G.IsBipartiteWith L R) (hcover : L ∪ R = Set.univ)
    (d : ℕ) (hd : 1 ≤ d)
    (h : ∀ S : Finset L, S.card - d ≤ (S.biUnion (fun x => G.neighborFinset x)).card) :
    ∃ M : G.Subgraph, M.IsMatching ∧ L.ncard - d ≤ M.edgeSet.ncard := by sorry

end YogeshwaranDM
