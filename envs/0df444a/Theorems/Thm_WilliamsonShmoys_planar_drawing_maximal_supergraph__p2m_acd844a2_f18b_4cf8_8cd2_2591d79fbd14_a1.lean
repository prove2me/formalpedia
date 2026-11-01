-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:42.260584+00:00
-- url     : https://prove2.me/theorems/4d05bb9d-42a1-4f6c-b6b4-be7b1a8f6d1e
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   Every graph with a supplied planar drawing has a planar supergraph on the same vertices that is maximal among planar supergraphs; the extension contains all original edges, so its edge count is at least the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
