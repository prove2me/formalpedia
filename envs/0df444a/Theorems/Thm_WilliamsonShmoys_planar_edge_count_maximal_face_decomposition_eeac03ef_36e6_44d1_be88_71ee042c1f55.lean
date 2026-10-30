-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_face_decomposition_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- name    : WilliamsonShmoys.planar_edge_count_maximal_face_decomposition_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:29:24.176513+00:00
-- url     : https://prove2.me/theorems/924dec2a-6dae-4338-b699-c87a63db146c
-- title:
--   Euler and face-incidence equations for a maximal drawable graph
-- statement:
--   For a maximal drawable simple graph on at least three vertices, produce a face count satisfying Euler’s equation and triangular face-edge incidence. The child removes the topological counting step from the parent. Its independent proof route is to obtain a plane embedding from the given drawing, use maximality to establish connectedness and triangular faces, then apply Euler’s formula and count edge-face incidences. The boundary case of three vertices is retained. This is the core obligation still requiring proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_maximal_face_decomposition_eeac03ef_36e6_44d1_be88_71ee042c1f55 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧ 3 * f = 2 * M.edgeSet.ncard := by sorry
