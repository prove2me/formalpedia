-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_maximal_count_957bde25
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_for_maximal_count_957bde25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:03:07.637898+00:00
-- url     : https://prove2.me/theorems/043ed921-cf29-4a86-9b71-b893941e8e60
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite vertex type has a supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_for_maximal_count_957bde25
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = K := by sorry
