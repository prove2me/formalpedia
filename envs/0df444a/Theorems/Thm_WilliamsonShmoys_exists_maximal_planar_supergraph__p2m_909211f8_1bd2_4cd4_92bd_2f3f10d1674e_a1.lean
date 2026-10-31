-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:41.607203+00:00
-- url     : https://prove2.me/theorems/dc3c3c5f-ee3d-4118-9c6e-a3edf0d67e38
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
    {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ W := by
  sorry
