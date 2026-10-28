-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:13:28.074792+00:00
-- url     : https://prove2.me/theorems/d0d93fef-7e80-449e-9049-1408f9160d0c
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   A maximal graph admitting the specified planar drawing on at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
