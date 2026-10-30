-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulated_edge_count
-- name    : WilliamsonShmoys.planar_drawing_extends_to_triangulated_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:28:55.049668+00:00
-- url     : https://prove2.me/theorems/f3b6ee58-cf22-4c54-9c5e-7a414d805147
-- title:
--   Planar drawing extends to a triangulated edge count
-- statement:
--   Every simple graph with a crossing-free drawing on a finite ordered vertex set of size at least three is an edge subgraph of another graph on the same vertices that also has a crossing-free drawing and exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_extends_to_triangulated_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      L.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
