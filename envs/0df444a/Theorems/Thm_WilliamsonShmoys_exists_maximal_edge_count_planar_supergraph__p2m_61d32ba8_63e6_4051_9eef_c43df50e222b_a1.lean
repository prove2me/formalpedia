-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_edge_count_planar_supergraph__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
-- name    : WilliamsonShmoys.exists_maximal_edge_count_planar_supergraph__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:56:58.504995+00:00
-- url     : https://prove2.me/theorems/3c1f8bc6-a5cd-402b-a3c7-948848f47e81
-- title:
--   Finite maximum edge count among drawable supergraphs
-- statement:
--   Every drawable finite graph has a drawable supergraph containing it whose edge count is at least that of every other drawable supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_edge_count_planar_supergraph__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
          M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
