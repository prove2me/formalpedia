-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_b54e7d04
-- name    : WilliamsonShmoys.planar_triangulation_completion_b54e7d04
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:40:36.759328+00:00
-- url     : https://prove2.me/theorems/7502da31-d18a-4d40-b7b3-c20c1448ca01
-- title:
--   Triangulated planar completion on a fixed vertex set
-- statement:
--   A finite simple graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertex set with exactly `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_b54e7d04
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
