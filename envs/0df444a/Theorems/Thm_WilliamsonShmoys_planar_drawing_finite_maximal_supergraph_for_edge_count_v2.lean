-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_supergraph_for_edge_count_v2
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_for_edge_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:22:01.953356+00:00
-- url     : https://prove2.me/theorems/6e00d3d3-4607-476c-850e-5199e96eed45
-- title:
--   Finite maximal drawable supergraph for edge counting
-- statement:
--   A drawable graph on a finite vertex type is contained in a drawable supergraph maximal under edge inclusion. The size hypothesis is retained for use by the edge-count result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_for_edge_count_v2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M <= N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ ∀ K : SimpleGraph V, N <= K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
