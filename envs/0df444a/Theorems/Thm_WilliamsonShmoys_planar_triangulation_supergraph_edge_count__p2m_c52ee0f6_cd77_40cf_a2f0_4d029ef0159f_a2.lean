-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:44:16.311243+00:00
-- url     : https://prove2.me/theorems/cc6eda38-1b75-4537-8542-c84b46a8d9a9
-- title:
--   Triangulated planar supergraph with maximal edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
