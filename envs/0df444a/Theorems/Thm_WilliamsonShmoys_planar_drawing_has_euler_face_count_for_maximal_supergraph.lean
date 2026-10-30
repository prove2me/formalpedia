-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_count_for_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_has_euler_face_count_for_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:39:18.627384+00:00
-- url     : https://prove2.me/theorems/d25638fd-76ba-4208-be1c-7efa0f5b3459
-- title:
--   Euler face count for a maximal drawable supergraph
-- statement:
--   A drawable graph maximal among drawable supergraphs containing W, on at least three vertices, has a natural face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_euler_face_count_for_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (W X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hWX : forall u v, W.Adj u v -> X.Adj u v)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, W.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat,
      (Fintype.card V : Int) - (X.edgeSet.ncard : Int) + (f : Int) = 2 := by sorry
