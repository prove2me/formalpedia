-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_exists
-- name    : WilliamsonShmoys.planar_triangulation_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:03:10.424809+00:00
-- url     : https://prove2.me/theorems/d47c52e0-25bc-4a91-9927-796873755464
-- title:
--   A drawable maximal-edge supergraph exists
-- statement:
--   For any simple graph on a finite linearly ordered vertex type with at least three vertices, there is a drawable supergraph on the same vertices with exactly 3n−6 edges. The result is independent of the original graph’s drawing; the supergraph can be constructed as a triangulation of vertices placed in convex position.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
