-- Prove2me | Theorems.Thm_WilliamsonShmoys_ncard_maximal_implies_maximal__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
-- name    : WilliamsonShmoys.ncard_maximal_implies_maximal__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:36.877201+00:00
-- url     : https://prove2.me/theorems/0d9f2874-65ad-4366-af70-67b5be8c7adf
-- title:
--   Maximum edge-set cardinality implies maximality
-- statement:
--   If every drawable supergraph of L has at most as many edges as L, then every drawable supergraph containing L equals L.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.ncard_maximal_implies_maximal__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
