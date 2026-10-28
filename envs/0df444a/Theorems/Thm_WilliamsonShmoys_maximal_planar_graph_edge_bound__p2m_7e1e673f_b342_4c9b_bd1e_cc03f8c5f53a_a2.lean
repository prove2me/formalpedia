-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:32:05.875698+00:00
-- url     : https://prove2.me/theorems/8b750c99-2508-4fa0-8f72-2f809c05bba0
-- title:
--   An inclusion-maximal drawable graph has at least 3n−6 edges
-- statement:
--   If R is drawable on at least three vertices and no drawable supergraph on the same vertex set strictly contains it, then R has at least 3n−6 edges. The proof route is the planar maximal-graph edge bound: establish connectedness and triangular faces from maximality, then combine the face-degree count with Euler’s formula. This isolates the geometric and extremal work needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn S →
      (∀ u v, R.Adj u v → S.Adj u v) → S = R) :
    3 * Fintype.card V - 6 <= R.edgeSet.ncard := by sorry
