-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a2
-- name    : WilliamsonShmoys.planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:14.424678+00:00
-- url     : https://prove2.me/theorems/e5953786-4eb4-4e6c-bc80-19f0610c5350
-- title:
--   Join disconnected planar components in one step with at least three vertices
-- statement:
--   If a finite linearly ordered vertex type has at least three vertices, every disconnected graph with a crossing-free drawing has a planar supergraph on the same vertices that makes a previously unreachable pair reachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V)
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hnot : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ K.Reachable u v := by sorry
