-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_repair3
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_extension_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:10:59.63026+00:00
-- url     : https://prove2.me/theorems/7a52924e-f958-460f-bd73-9ec412a15ac4
-- title:
--   Finite maximal drawable extension (repair 3)
-- statement:
--   Any drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type. Choose a drawable supergraph with the greatest edge count; any drawable graph containing it must then have the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_finite_maximal_extension_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
