-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_drawable_supergraph_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:16:50.593396+00:00
-- url     : https://prove2.me/theorems/3082665e-784a-4fb1-af0e-05d4524669ec
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph_419a1fb2_144c_4e12_b921_930e8d46d3d3 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) : ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
