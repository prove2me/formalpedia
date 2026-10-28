-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_retry2
-- name    : WilliamsonShmoys.maximal_planar_face_count_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:05:33.168392+00:00
-- url     : https://prove2.me/theorems/d0136c19-2d78-4fd7-bad5-4a5a95752e1b
-- title:
--   Euler and triangular-face count for a maximal planar drawing
-- statement:
--   A maximal simple graph on at least three vertices with a crossing-free drawing has a face count satisfying both Euler’s equation and the triangular face-edge incidence count. Prove connectedness and triangularity from maximality, handle the three-vertex triangle case, then count incidences and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    exists f : Nat,
      3 * (f : Int) = 2 * (M.edgeSet.ncard : Int) /\
      (Fintype.card V : Int) - (M.edgeSet.ncard : Int) + (f : Int) = 2 := by sorry
