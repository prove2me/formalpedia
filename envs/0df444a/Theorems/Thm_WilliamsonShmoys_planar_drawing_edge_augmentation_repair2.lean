-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_repair2
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:23:01.625422+00:00
-- url     : https://prove2.me/theorems/772ef201-63b7-4b42-b9f5-1f5abd1bb02f
-- title:
--   Edge augmentation below the planar bound
-- statement:
--   If a drawable graph on at least three vertices has fewer than 3|V|−6 edges, it has a drawable strict supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_augmentation_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hE : N.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V, N < M ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by
  sorry
