-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
-- name    : WilliamsonShmoys.planar_drawing_add_bridge__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:26.071719+00:00
-- url     : https://prove2.me/theorems/b16f7d24-87bc-4095-88fe-fe2dcb83034c
-- title:
--   Insert a bridge into a disconnected planar drawing
-- statement:
--   For a finite graph with the given crossing-free drawing, if the graph is disconnected, there is a supergraph on the same vertices that still has such a drawing and contains an edge joining two vertices that were in different components. The exact drawing predicate requires constructing an arc for the new edge that meets old edges only at shared endpoints. The claim also covers isolated vertices and singleton components; these do not create exceptions to the desired geometric construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_bridge__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v, ¬ G.Reachable u v ∧ K.Adj u v := by sorry
