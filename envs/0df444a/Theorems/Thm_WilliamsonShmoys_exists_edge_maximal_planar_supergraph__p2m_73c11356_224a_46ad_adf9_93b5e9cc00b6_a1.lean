-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:32:59.165078+00:00
-- url     : https://prove2.me/theorems/ce5da3a5-6829-4f27-a8ae-e3e80a750393
-- title:
--   Every planar graph has an edge-maximal planar supergraph on the same vertices
-- statement:
--   Every planar simple graph on a finite linearly ordered vertex type has a planar supergraph on the same vertices that is maximal under graph inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
