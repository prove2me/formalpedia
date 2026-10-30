-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T19:58:12.175016+00:00
-- url     : https://prove2.me/theorems/73f2721b-9638-40de-84f2-73b0dfd4838a
-- title:
--   Euler upper bound for a finite planar graph
-- statement:
--   A finite simple graph with a planar drawing and at least three vertices has at most 3|V|−6 edges. This is the usual Euler planar edge bound, including graphs that are disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
