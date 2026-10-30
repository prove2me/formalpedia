-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_has_triangulation_count_c1858b2a_2070_4db6_a0f4_ae5f3dacb3cc
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_has_triangulation_count_c1858b2a_2070_4db6_a0f4_ae5f3dacb3cc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:53:33.761459+00:00
-- url     : https://prove2.me/theorems/f527a548-06f5-4b5c-945f-b0c46bc40c81
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_has_triangulation_count_c1858b2a_2070_4db6_a0f4_ae5f3dacb3cc
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S)
    (hCard : 3 ≤ Fintype.card V) :
    S.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
