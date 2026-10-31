-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:08.93409+00:00
-- url     : https://prove2.me/theorems/5044aa6a-f37f-461e-b852-1ca819824640
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type is contained in a drawable graph maximal under inclusion among drawable supergraphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P →
        WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
