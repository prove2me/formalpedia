-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:46:39.311414+00:00
-- url     : https://prove2.me/theorems/b62fe045-07aa-4f54-ba33-572ba82c4c90
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type whose edge count is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_finite
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
