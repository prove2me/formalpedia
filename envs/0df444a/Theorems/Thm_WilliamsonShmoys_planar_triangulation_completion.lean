-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion
-- name    : WilliamsonShmoys.planar_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:30:29.142536+00:00
-- url     : https://prove2.me/theorems/169089d4-7912-4bcb-aa40-6124e93dc9d4
-- title:
--   Triangulated planar completion on the same vertex set
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices is a subgraph of a graph on the same vertex set that has a crossing-free drawing and exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
