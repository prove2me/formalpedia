-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:08.722196+00:00
-- url     : https://prove2.me/theorems/0b3013ac-25d6-4dd0-b6f8-fc82fd3d8fbf
-- title:
--   Every finite planar graph has a maximal planar supergraph on the same vertices
-- statement:
--   Any finite planar simple graph has a planar supergraph on the same vertices that admits no strictly larger planar simple supergraph on those vertices. The vertex-count hypothesis is retained for the companion edge-count result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeFinset ⊆ K.edgeFinset ∧
      (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeFinset ⊆ L.edgeFinset → K.edgeFinset = L.edgeFinset) := by
  sorry
