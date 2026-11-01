-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_fixed_bridge__p2m_b16f7d24_87bc_4095_88fe_fe2dcb83034c_a1
-- name    : WilliamsonShmoys.planar_drawing_add_fixed_bridge__p2m_b16f7d24_87bc_4095_88fe_fe2dcb83034c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:53.763741+00:00
-- url     : https://prove2.me/theorems/78f08617-f09f-420a-8722-a9fd1ddbf5be
-- title:
--   Add a bridge between fixed vertices in different components
-- statement:
--   For any two vertices that are not reachable from one another in a finite graph with the given crossing-free drawing, there is a supergraph on the same vertices that still has such a drawing and contains the edge joining those fixed vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_fixed_bridge__p2m_b16f7d24_87bc_4095_88fe_fe2dcb83034c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hSeparate : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Adj u v := by
  sorry
