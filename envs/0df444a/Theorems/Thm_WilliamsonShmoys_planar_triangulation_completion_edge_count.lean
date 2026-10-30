-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:54:41.666331+00:00
-- url     : https://prove2.me/theorems/e9ce3df1-a197-4828-a24c-84c363604464
-- title:
--   Planar graphs extend to triangulations with the exact edge count
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
