-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_for_drawing
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:07:53.044859+00:00
-- url     : https://prove2.me/theorems/f7a4937f-b285-44cd-b3f2-a3428ab9639b
-- title:
--   Maximal planar edge count lower bound for the supplied drawing predicate
-- statement:
--   An inclusion-maximal graph under `IsMaximalPlanarOn` with at least three vertices has at least three times its vertex count minus six edges. This includes exactly three vertices. A proof route is to derive connectedness and triangular faces from maximality—an addable diagonal would contradict maximality—and then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKmax : IsMaximalPlanarOn K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
