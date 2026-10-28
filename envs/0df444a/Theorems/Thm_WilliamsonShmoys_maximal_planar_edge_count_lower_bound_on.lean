-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_on
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_on
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:19:51.699138+00:00
-- url     : https://prove2.me/theorems/12fa1253-0a8c-46a3-923f-0a4528e96903
-- title:
--   Lower edge count for a maximal planar graph
-- statement:
--   An inclusion-maximal graph with the specified planar drawing on at least three finite ordered vertices has at least three times its vertex count minus six edges. At n = 3, maximality forces the triangle. The standard proof uses maximality to establish a connected triangulation, then Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_on
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHmax : WilliamsonShmoys.IsMaximalPlanarOn H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
