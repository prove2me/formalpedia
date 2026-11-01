-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:56.473594+00:00
-- url     : https://prove2.me/theorems/4cf1e2b2-149e-4f7a-8404-753e093946ad
-- title:
--   Existence of an edge maximal planar supergraph
-- statement:
--   Every finite planar graph on a fixed ordered vertex type has a planar supergraph on that same type that is maximal under adjacency inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        (∀ u v, N.Adj u v → P.Adj u v) → P = N) := by sorry
