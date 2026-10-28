-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_repair3
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:30:28.7361+00:00
-- url     : https://prove2.me/theorems/1b39b828-58fc-4ef1-a477-eeaba85e9424
-- title:
--   Triangulation extension for a crossing-free drawing (repair 3)
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges. This isolates the plane-embedding triangulation and Euler-counting work; the parent applies maximality to identify the supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
