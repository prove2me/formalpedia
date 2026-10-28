-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:38:23.93619+00:00
-- url     : https://prove2.me/theorems/4660a2bb-aa2d-46e6-b847-cba091ca7c82
-- title:
--   Add a planar drawing edge between components
-- statement:
--   Given a disconnected finite graph with a crossing-free drawing under the exact `HasPlanarDrawingOn` definition, one can add an edge between two previously unreachable vertices while retaining such a drawing. The required new argument is to find and formalize an arc through the drawing's complement, with all existing arcs and vertices avoided except at its endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
