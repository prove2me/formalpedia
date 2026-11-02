-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
-- name    : WilliamsonShmoys.planar_supergraph_max_card__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:18.739669+00:00
-- url     : https://prove2.me/theorems/e16821ba-ba0f-4641-89ea-cdad8056fc2b
-- title:
--   Planar supergraph with maximum edge count
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices whose edge count is at least that of every planar supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_supergraph_max_card__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeFinset ⊆ K.edgeFinset ∧
      (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        G.edgeFinset ⊆ L.edgeFinset →
        L.edgeFinset.card ≤ K.edgeFinset.card) := by sorry
