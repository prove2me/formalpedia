-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension_ncard__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension_ncard__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:33.882268+00:00
-- url     : https://prove2.me/theorems/0f7b0715-7a61-4d18-9161-7b6fbd4954a3
-- title:
--   A drawable extension with maximum edge-set cardinality exists
-- statement:
--   Among drawable supergraphs of K, there is one with at least as many edges as every other drawable supergraph of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_extension_ncard__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
          M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
