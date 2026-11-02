-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_card_maximal_planar_extension__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
-- name    : WilliamsonShmoys.exists_card_maximal_planar_extension__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:51:59.540525+00:00
-- url     : https://prove2.me/theorems/16fb1a0d-e68c-4595-a206-2f4554b0589b
-- title:
--   A drawable extension of maximum edge count exists
-- statement:
--   Among the drawable supergraphs of N, one has edge-set cardinality at least that of every other drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_card_maximal_planar_extension__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
