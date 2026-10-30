-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:16:20.733166+00:00
-- url     : https://prove2.me/theorems/b5ff312f-9e3b-457f-a651-ee112e7c9cf9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   This child contributes the core planar-graph theorem: a drawable graph on at least three vertices that has no strict drawable extension has exactly 3|V|−6 edges. Its proof route is to use the crossing-free drawing to augment disconnected components within faces, then add noncrossing diagonals until faces are triangles, and apply Euler's formula; maximality forces the original graph already to have the resulting edge count. The hypotheses retain the vertex lower bound needed for the triangulation formula. This is the remaining substantive obligation in the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ X : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn X → W ≤ X → X ≤ W) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
