-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:34.742022+00:00
-- url     : https://prove2.me/theorems/ec0d3647-502d-42fc-b1da-31eb94cbd70b
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal under graph inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
