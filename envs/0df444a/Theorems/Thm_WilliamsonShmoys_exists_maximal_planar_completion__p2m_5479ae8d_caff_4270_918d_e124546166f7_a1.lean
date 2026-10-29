-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:34:04.709869+00:00
-- url     : https://prove2.me/theorems/9537482d-6a1a-4251-8ad1-af2d4cae6a52
-- title:
--   Existence of a maximal planar completion
-- statement:
--   Every finitely vertex-labeled planar graph has a planar supergraph on the same vertices that is maximal under inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ N : SimpleGraph V,
      L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph V, N ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N := by sorry
