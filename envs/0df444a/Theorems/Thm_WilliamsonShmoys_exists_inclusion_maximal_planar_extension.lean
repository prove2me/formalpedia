-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_extension
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:55:55.589234+00:00
-- url     : https://prove2.me/theorems/0f8f3774-5919-4466-b67b-3f8e0d9bf6c6
-- title:
--   Every finite planar graph has an inclusion-maximal planar extension
-- statement:
--   Every finite graph with a planar drawing is contained in an inclusion-maximal planar graph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ IsMaximalPlanarOn K := by sorry
