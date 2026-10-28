-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_lower_20261026
-- name    : WilliamsonShmoys.planar_drawing_edge_count_lower_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:01:39.612857+00:00
-- url     : https://prove2.me/theorems/79258336-4d77-4999-9500-8457582dcd61
-- title:
--   Lower bound from edge maximality
-- statement:
--   A graph maximal among graphs on the same vertex type admitting the specified drawing, with at least three vertices, has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_count_lower_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hPmax : ∀ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Q) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
