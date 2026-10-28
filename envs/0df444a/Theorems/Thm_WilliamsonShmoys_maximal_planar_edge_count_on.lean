-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_on
-- name    : WilliamsonShmoys.maximal_planar_edge_count_on
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T19:57:57.075867+00:00
-- url     : https://prove2.me/theorems/04ad0724-f3eb-4cdb-bfae-377fc9e8cb33
-- title:
--   Edge count of a maximal planar graph on a fixed vertex set
-- statement:
--   Every inclusion-maximal drawable graph on at least three finite ordered vertices has exactly three times the vertex count minus six edges. This provides the numerical conclusion for the parent. A proof proceeds through connectedness and triangular faces, then Euler’s formula and face-edge incidence counting. The hypothesis of at least three vertices is essential to the stated planar edge formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_on
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHmax : IsMaximalPlanarOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
