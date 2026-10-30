-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:49:29.978518+00:00
-- url     : https://prove2.me/theorems/d3397ab1-6904-4f5b-9f42-97dace9610cf
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph is contained in an inclusion-maximal drawable graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by
  sorry
