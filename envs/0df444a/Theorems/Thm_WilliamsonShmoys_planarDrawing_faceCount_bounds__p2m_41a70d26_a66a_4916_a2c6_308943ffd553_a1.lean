-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_faceCount_bounds__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
-- name    : WilliamsonShmoys.planarDrawing_faceCount_bounds__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:15.326828+00:00
-- url     : https://prove2.me/theorems/75c1dbe5-597b-4ab5-bcaf-dc768f4756d8
-- title:
--   Face count bounds for a connected planar drawing
-- statement:
--   For a connected graph with at least three vertices and a drawing as defined by HasPlanarDrawingOn, there is a finite face count f satisfying Euler’s equation and the inequality that three times the number of faces is at most twice the number of edges. The inequality counts both sides of bridge edges. This removes the geometric face decomposition and incidence accounting from the parent; a proof route is to form the faces of the embedded finite graph, apply Euler’s formula, and count the boundary walks, including both traversals of every bridge. The remaining core obligation is establishing these facts for the exact continuous-arc drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_faceCount_bounds__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (hconn : U.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     ∃ f : Nat,
       Fintype.card V + f = U.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * U.edgeFinset.card) := by sorry
