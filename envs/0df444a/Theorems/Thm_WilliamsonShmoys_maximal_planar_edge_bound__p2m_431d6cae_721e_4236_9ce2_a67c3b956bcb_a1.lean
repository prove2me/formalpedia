-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:56:08.747191+00:00
-- url     : https://prove2.me/theorems/0e98e963-983c-4fb9-9e38-7bdda2495dff
-- title:
--   Euler edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge-inclusion has at most 3|V|−6 edges; the Euler argument gives equality for such a maximal graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
