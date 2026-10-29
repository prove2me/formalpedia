-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:39:42.837873+00:00
-- url     : https://prove2.me/theorems/c881480e-572e-4728-9775-9ce4f807e342
-- title:
--   Exact edge count for a triangulation extension
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ 3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
