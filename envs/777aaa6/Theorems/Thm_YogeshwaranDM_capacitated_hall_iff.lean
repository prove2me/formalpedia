-- Prove2me | Theorems.Thm_YogeshwaranDM_capacitated_hall_iff
-- name    : YogeshwaranDM.capacitated_hall_iff
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:43:42.962951+00:00
-- url     : https://prove2.me/theorems/f1407fe3-454d-4f5e-bd13-d9ce072c3085
-- title:
--   Exercise 6.5 — Hall's criterion with prescribed left degrees
-- statement:
--   **Exercise 6.5 — Hall's criterion with prescribed left degrees.** Let $G$ be a finite simple bipartite graph with vertex partition $L\sqcup R$. For every $x\in L$, prescribe a demand $d_x\in\mathbb N$, allowing zero. Then
--   $$
--   \begin{split}
--   &\exists H\subseteq G:\
--      \bigl(\forall x\in L,\ \deg_H(x)=d_x\bigr)
--      \quad\land\quad
--      \bigl(\forall y\in R,\ \deg_H(y)\le1\bigr)\\
--   &\hspace{20mm}\Longleftrightarrow\quad
--      \forall S\subseteq L,\ \sum_{x\in S}d_x\le |N_G(S)|.
--   \end{split}
--   $$
--
--   **Formalization note.** The witness is an actual native subgraph, not a fractional allocation or an assumed matching. A vertex's degree is the cardinality of its neighbor set in that subgraph, with degree zero outside the subgraph's vertex set. All finite cardinalities and all demands are natural numbers.
-- source:
--   D. Yogeshwaran, Discrete Mathematics—Lecture Notes, Indian Statistical Institute Bangalore, HTML edition generated May 9, 2025, Exercise(A) 6.5, https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch6.S1.html

import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace YogeshwaranDM

theorem capacitated_hall_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (L R : Set V) (hG : G.IsBipartiteWith L R)
    (hcover : L ∪ R = Set.univ) (d : L → ℕ) :
    (∃ H : G.Subgraph, (∀ x : L, (H.neighborSet x).ncard = d x) ∧
      ∀ y ∈ R, (H.neighborSet y).ncard ≤ 1) ↔
      ∀ S : Finset L, ∑ x ∈ S, d x ≤ (S.biUnion (fun x => G.neighborFinset x)).card := by sorry

end YogeshwaranDM
