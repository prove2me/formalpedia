-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension
-- name    : WilliamsonShmoys.planar_graph_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:53:16.503032+00:00
-- url     : https://prove2.me/theorems/141bbd3b-134e-4a34-ad12-6a87c37f460e
-- title:
--   Planar graph extension to a triangulation with fixed vertex set
-- statement:
--   Every finite planar graph on a fixed ordered vertex type of size at least three has a planar supergraph on the same vertex set whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
