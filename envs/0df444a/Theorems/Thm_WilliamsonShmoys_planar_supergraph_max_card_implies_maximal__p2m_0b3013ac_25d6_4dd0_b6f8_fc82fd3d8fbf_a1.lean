-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card_implies_maximal__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
-- name    : WilliamsonShmoys.planar_supergraph_max_card_implies_maximal__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:21.959095+00:00
-- url     : https://prove2.me/theorems/4e384b11-a99e-458c-a16b-f6deb5a87c64
-- title:
--   Maximum edge count implies inclusion maximality
-- statement:
--   If a planar supergraph has at least as many edges as every planar supergraph containing the original graph, then it has no strictly larger planar supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_supergraph_max_card_implies_maximal__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsub : G.edgeFinset ⊆ K.edgeFinset)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      G.edgeFinset ⊆ L.edgeFinset →
      L.edgeFinset.card ≤ K.edgeFinset.card) :
    ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset →
      K.edgeFinset = L.edgeFinset := by sorry
