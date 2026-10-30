-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_20f2cea7
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_lower_20f2cea7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:44:32.412107+00:00
-- url     : https://prove2.me/theorems/6495d18e-9006-4427-99d6-7edc5376090e
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A graph maximal among graphs admitting the specified drawing, on at least three vertices, has at least `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_edge_count_lower_20f2cea7
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
