-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:55:57.425088+00:00
-- url     : https://prove2.me/theorems/166d44ba-f923-42a0-82cc-8fc3a6ee7e5c
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = H := by
  sorry
