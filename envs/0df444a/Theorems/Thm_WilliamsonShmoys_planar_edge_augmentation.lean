-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation
-- name    : WilliamsonShmoys.planar_edge_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:30:15.882269+00:00
-- url     : https://prove2.me/theorems/0d04d785-fba1-41e9-8e1e-3c9a4bbcca0f
-- title:
--   A drawable graph below the edge bound admits one more edge
-- statement:
--   If a finite drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, one missing edge can be added while retaining a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hE : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = M.edgeSet.ncard + 1 := by sorry
