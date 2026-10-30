-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_planar_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:10:15.625564+00:00
-- url     : https://prove2.me/theorems/6bc6440f-e2a7-4cff-842e-e5136595172f
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges. Its boundary case is three vertices, where maximality forces the triangle; in general the proof uses triangulation and Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ Y : SimpleGraph V, Z ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = Z) :
    3 * Fintype.card V = Z.edgeSet.ncard + 6 := by sorry
