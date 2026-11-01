-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximizer__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_maximizer__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:14.192055+00:00
-- url     : https://prove2.me/theorems/f396ad70-53cd-4e6b-abdb-b25f4fc5b7dc
-- title:
--   Drawable supergraph maximizing edge count
-- statement:
--   Every drawable graph on the given finite vertex type has a drawable supergraph whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_maximizer__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
          K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
