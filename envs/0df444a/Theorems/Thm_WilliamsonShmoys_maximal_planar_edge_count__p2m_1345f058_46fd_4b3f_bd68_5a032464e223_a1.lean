-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:53:19.975528+00:00
-- url     : https://prove2.me/theorems/4c00200f-eeb1-41b9-b1b1-6e3542741a6b
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable proper simple supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ∀ u v, K.Adj u v → H.Adj u v) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
