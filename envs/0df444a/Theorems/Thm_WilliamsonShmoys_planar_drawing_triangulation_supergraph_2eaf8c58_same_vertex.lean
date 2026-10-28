-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex
-- name    : WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:31:25.650027+00:00
-- url     : https://prove2.me/theorems/674b0094-2468-483e-83ab-bb18dbc55990
-- title:
--   Triangulated drawable supergraph on the same vertices
-- statement:
--   Every finite graph with the supplied crossing-free drawing and at least three vertices has a drawable supergraph on the same vertex set with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
