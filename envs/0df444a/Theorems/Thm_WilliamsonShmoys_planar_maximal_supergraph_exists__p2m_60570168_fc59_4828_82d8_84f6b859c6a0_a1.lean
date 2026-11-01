-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:56:38.660798+00:00
-- url     : https://prove2.me/theorems/43a8702e-3dc0-47b3-8ebe-24ea9f69582f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M ≤ K := by sorry
