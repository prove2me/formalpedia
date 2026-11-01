-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:19.513057+00:00
-- url     : https://prove2.me/theorems/2ae65a7c-57f2-4cef-ba44-e42518b858bb
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable edge extensions has at least 3|V|−6 edges. This supplies the extremal estimate needed by the parent. A proof route is to use maximality to establish the connectivity and face structure of a maximal planar graph, then formalize Euler’s formula and count edge-face incidences. The case of at least three vertices is essential to the stated bound; the remaining core obligation is this topological argument for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (X : SimpleGraph V) (dX : DecidableRel X.Adj),
      HasPlanarDrawingOn X →
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel X.Adj := dX
       W.edgeFinset ⊆ X.edgeFinset) →
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel X.Adj := dX
       X.edgeFinset ⊆ W.edgeFinset)) :
    3 * Fintype.card V - 6 ≤ (letI : DecidableRel W.Adj := dW; W.edgeFinset.card) := by sorry
