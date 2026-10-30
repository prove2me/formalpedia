-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_spanning_triangulation_extension
-- name    : WilliamsonShmoys.planar_spanning_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:48:29.812344+00:00
-- url     : https://prove2.me/theorems/4685f39c-4356-47d7-b134-2b986f94c2d5
-- title:
--   Every finite planar graph extends to a spanning triangulation
-- statement:
--   Any simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three is a spanning subgraph of a planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_spanning_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K.edgeSet ⊆ K'.edgeSet ∧
      K'.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
