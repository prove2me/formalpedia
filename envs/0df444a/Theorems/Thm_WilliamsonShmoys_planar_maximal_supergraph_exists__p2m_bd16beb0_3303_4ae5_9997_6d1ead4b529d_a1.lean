-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:57.453905+00:00
-- url     : https://prove2.me/theorems/93e678ee-21d2-4500-aea7-026ed25bc307
-- title:
--   Finite maximal planar supergraph on the same vertices
-- statement:
--   Any graph with a crossing-free drawing on a finite vertex type is contained in an adjacency-maximal graph with a crossing-free drawing on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        (∀ u v, N.Adj u v → P.Adj u v) → P = N) := by sorry
