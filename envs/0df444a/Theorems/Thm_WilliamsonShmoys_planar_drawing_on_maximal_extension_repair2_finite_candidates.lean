-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension_repair2_finite_candidates
-- name    : WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_candidates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:13:17.622615+00:00
-- url     : https://prove2.me/theorems/3affbc94-2b24-41f1-b5f9-028452991f19
-- title:
--   Finiteness of planar drawing candidates
-- statement:
--   For a finite vertex type, the set of drawable simple graphs containing a fixed graph is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_candidates
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    Set.Finite {M : SimpleGraph V | G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M} := by
  sorry
