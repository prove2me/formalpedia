-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:53:56.642373+00:00
-- url     : https://prove2.me/theorems/0eac1a5f-b1b6-46f5-825b-7fa3e660c5c4
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ M : SimpleGraph V,
        K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = K := by sorry
