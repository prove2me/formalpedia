-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
-- name    : WilliamsonShmoys.planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:30.595496+00:00
-- url     : https://prove2.me/theorems/89f0f1fe-2e03-43a1-bf2e-88524a63c447
-- title:
--   Join two disconnected planar components in one step
-- statement:
--   For a finite linearly ordered vertex type, if a graph has a crossing-free drawing and is disconnected, there is a planar supergraph on the same vertices that makes some formerly unreachable pair reachable. This is the geometric one-step claim. It is supported by the cited source's argument that components can be joined through a common unbounded face; formalizing the arc construction remains the core obligation. Disconnectedness rules out the empty and singleton cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hnot : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ K.Reachable u v := by sorry
