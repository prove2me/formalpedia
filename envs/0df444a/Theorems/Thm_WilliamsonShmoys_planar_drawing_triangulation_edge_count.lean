-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_count
-- name    : WilliamsonShmoys.planar_drawing_triangulation_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:08:05.576744+00:00
-- url     : https://prove2.me/theorems/95790cde-4e9b-4604-8aab-c170e1fe7b7a
-- title:
--   Triangulated planar supergraph edge count
-- statement:
--   Any finite planar drawing on at least three ordered vertices has a planar supergraph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_drawing_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
