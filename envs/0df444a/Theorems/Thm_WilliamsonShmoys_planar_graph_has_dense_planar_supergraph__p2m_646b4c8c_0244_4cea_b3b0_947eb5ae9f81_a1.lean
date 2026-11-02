-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_planar_supergraph__p2m_646b4c8c_0244_4cea_b3b0_947eb5ae9f81_a1
-- name    : WilliamsonShmoys.planar_graph_has_dense_planar_supergraph__p2m_646b4c8c_0244_4cea_b3b0_947eb5ae9f81_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:11.854493+00:00
-- url     : https://prove2.me/theorems/282f380d-4578-4570-b4a5-8b4767d8af92
-- title:
--   Dense drawable supergraph extension
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_dense_planar_supergraph__p2m_646b4c8c_0244_4cea_b3b0_947eb5ae9f81_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
