-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:43:27.572829+00:00
-- url     : https://prove2.me/theorems/88b90669-f7d4-4a9b-9847-ad94684907c7
-- title:
--   Existence of a maximal drawn supergraph
-- statement:
--   Every graph with the given drawing is contained in a drawn supergraph on the same vertex set that is maximal under edge inclusion; the original graph’s edge count is at most the supergraph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn J) :
    ∃ H : SimpleGraph V,
      J ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      J.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
