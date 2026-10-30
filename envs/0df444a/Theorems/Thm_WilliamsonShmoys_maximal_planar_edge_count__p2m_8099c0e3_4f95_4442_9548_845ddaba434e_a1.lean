-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:09.928641+00:00
-- url     : https://prove2.me/theorems/529ff6c9-d746-4547-9934-f47cc51c6339
-- title:
--   An edge-maximal planar graph has the triangulation edge count
-- statement:
--   A finite edge-maximal simple planar graph with at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
