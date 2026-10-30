-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_repair3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:13:52.018845+00:00
-- url     : https://prove2.me/theorems/721984f6-9522-4ccc-9bc4-86f01e08240e
-- title:
--   Edge bound for a maximal drawable graph (repair 3)
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3 * |V| - 6` edges. Maximality yields the standard maximal-planar edge bound, which follows from planar embedding structure and Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
