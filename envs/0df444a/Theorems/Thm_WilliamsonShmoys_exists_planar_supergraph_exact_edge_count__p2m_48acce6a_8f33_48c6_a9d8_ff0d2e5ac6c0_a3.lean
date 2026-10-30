-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_exact_edge_count__p2m_48acce6a_8f33_48c6_a9d8_ff0d2e5ac6c0_a3
-- name    : WilliamsonShmoys.exists_planar_supergraph_exact_edge_count__p2m_48acce6a_8f33_48c6_a9d8_ff0d2e5ac6c0_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:11:34.683984+00:00
-- url     : https://prove2.me/theorems/9b481115-396e-4251-a44a-4293d6576e9f
-- title:
--   A drawable graph has an exact edge-count completion
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex set of size at least three is contained in a graph on that same vertex set that also has a crossing-free drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_planar_supergraph_exact_edge_count__p2m_48acce6a_8f33_48c6_a9d8_ff0d2e5ac6c0_a3 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) (hV : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, N ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
