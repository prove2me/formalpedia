-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_upper_bound_edge_maximal_extension__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
-- name    : WilliamsonShmoys_maximal_planar_euler_upper_bound_edge_maximal_extension__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:03:57.217237+00:00
-- url     : https://prove2.me/theorems/646dfb24-703c-493f-8075-444718d53d7b
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every finite drawable simple graph is a subgraph of an inclusion-maximal drawable graph on the same vertices, with no fewer edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_euler_upper_bound_edge_maximal_extension__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
