-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- name    : WilliamsonShmoys.maximal_planar_extension_exists_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:24:53.189413+00:00
-- url     : https://prove2.me/theorems/06155f06-97cd-4b4b-986f-9f1d08bb40d7
-- title:
--   Existence of a maximal drawable planar extension
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_exists_419a1fb2_144c_4e12_b921_930e8d46d3d3 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
