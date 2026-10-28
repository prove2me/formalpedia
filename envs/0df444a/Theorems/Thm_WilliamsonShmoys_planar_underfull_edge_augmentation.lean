-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_underfull_edge_augmentation
-- name    : WilliamsonShmoys.planar_underfull_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:09:03.445264+00:00
-- url     : https://prove2.me/theorems/7bb986fa-cc60-4171-bd66-8c1485a93a8f
-- title:
--   Adding an edge to an underfull planar drawing
-- statement:
--   If a drawable simple graph on at least three vertices has strictly fewer than 3|V|−6 edges, some missing edge can be added while preserving a planar drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_underfull_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hunderfull : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      M.edgeSet ≠ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
