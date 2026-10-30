-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_with_maximal_edge_count
-- name    : WilliamsonShmoys.planar_extension_with_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:47:47.075891+00:00
-- url     : https://prove2.me/theorems/1d408539-34dc-4d00-a520-e1beba581442
-- title:
--   Planar extension to a triangulated edge count
-- statement:
--   Any graph with a crossing-free drawing on at least three fixed vertices has a crossing-free supergraph on those same vertices with exactly three times the number of vertices minus six edges. The child removes the topological augmentation and Euler-counting work from the parent. An independent proof route is to add noncrossing edges until every face is triangular, then count face-edge incidences using Euler's formula; the three-vertex case is the triangle. The precise augmentation argument for the arc-based drawing predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_with_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
