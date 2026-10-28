-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_repair_3e188728
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_repair_3e188728
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:04:54.025239+00:00
-- url     : https://prove2.me/theorems/200e4132-39b7-49b4-ad60-e78c02419265
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal under inclusion among drawable supergraphs. A proof can maximize edge count over the finite collection of drawable supergraphs containing Y.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_repair_3e188728
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hV : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V,
      Y ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
