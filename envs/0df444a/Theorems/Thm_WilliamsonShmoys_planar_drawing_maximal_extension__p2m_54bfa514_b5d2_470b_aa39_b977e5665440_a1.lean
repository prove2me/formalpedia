-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:51.354042+00:00
-- url     : https://prove2.me/theorems/f0005e3e-fded-4b57-acf4-9bb9b5d27ef1
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices. The vertex bound is retained for use by the edge-count result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn J) :
    ∃ N : SimpleGraph V,
      J ≤ N ∧
      HasPlanarDrawingOn N ∧
      (∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) := by sorry
