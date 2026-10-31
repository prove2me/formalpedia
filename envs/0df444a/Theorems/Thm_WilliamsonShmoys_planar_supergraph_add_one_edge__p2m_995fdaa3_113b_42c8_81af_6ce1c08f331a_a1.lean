-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_add_one_edge__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- name    : WilliamsonShmoys.planar_supergraph_add_one_edge__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:13.938117+00:00
-- url     : https://prove2.me/theorems/9eb5f952-9b4b-4697-87c0-694ff39636a3
-- title:
--   A larger drawable supergraph yields one drawable edge addition
-- statement:
--   If a drawable graph is a strict subgraph of a drawable graph on the same finite vertices, it has a drawable supergraph with exactly one more edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_add_one_edge__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1 {V : Type} [Fintype V] [LinearOrder V] (M N : SimpleGraph V) (hMN : M.edgeSet ⊆ N.edgeSet) (hDrawM : WilliamsonShmoys.HasPlanarDrawingOn M) (hDrawN : WilliamsonShmoys.HasPlanarDrawingOn N) (hcard : M.edgeSet.ncard < N.edgeSet.ncard) : ∃ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = M.edgeSet.ncard + 1 := by sorry
