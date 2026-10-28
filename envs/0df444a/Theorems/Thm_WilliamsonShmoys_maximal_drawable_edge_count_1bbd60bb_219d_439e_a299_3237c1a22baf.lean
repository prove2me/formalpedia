-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_1bbd60bb_219d_439e_a299_3237c1a22baf
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_1bbd60bb_219d_439e_a299_3237c1a22baf
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:56:30.308526+00:00
-- url     : https://prove2.me/theorems/05f6ed0a-87c9-4f2d-b456-23e30c0f5111
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph with at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_1bbd60bb_219d_439e_a299_3237c1a22baf
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
