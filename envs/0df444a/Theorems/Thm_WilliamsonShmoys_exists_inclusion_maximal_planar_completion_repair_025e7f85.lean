-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_completion_repair_025e7f85
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_completion_repair_025e7f85
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:57:26.966289+00:00
-- url     : https://prove2.me/theorems/f383b9f7-81be-4999-8f99-8bd17367dcea
-- title:
--   Existence of a maximal drawable completion
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_completion_repair_025e7f85 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
