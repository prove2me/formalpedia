-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_edge_bound_target
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_for_edge_bound_target
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:48:52.908999+00:00
-- url     : https://prove2.me/theorems/8922ad49-0f12-4fdc-92d4-c92d5704ef0e
-- title:
--   Maximal planar extension for the edge bound
-- statement:
--   Every graph admitting the given planar drawing has an inclusion-maximal planar supergraph on the same finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_extension_for_edge_bound_target {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
