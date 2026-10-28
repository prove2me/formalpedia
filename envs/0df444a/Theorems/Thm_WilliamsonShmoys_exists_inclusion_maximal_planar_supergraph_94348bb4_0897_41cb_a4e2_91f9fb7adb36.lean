-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_94348bb4_0897_41cb_a4e2_91f9fb7adb36
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_94348bb4_0897_41cb_a4e2_91f9fb7adb36
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:34:24.73165+00:00
-- url     : https://prove2.me/theorems/8d9f54ce-7c42-406d-aabf-3ef47e45c2f4
-- title:
--   A finite planar graph has a maximal planar supergraph on the same vertices
-- statement:
--   Every finite graph with a crossing-free drawing has an inclusion maximal planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_94348bb4_0897_41cb_a4e2_91f9fb7adb36 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
