-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_incidence_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangular_incidence_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:42:48.400819+00:00
-- url     : https://prove2.me/theorems/94fe7ade-67af-4d0f-8c97-4b852ca16eac
-- title:
--   Triangular face incidence count for a maximal drawable graph
-- statement:
--   For a maximal drawable supergraph of W with at least three vertices, any natural face count satisfying Euler’s equation satisfies the triangular edge-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangular_incidence_count
    {V : Type} [Fintype V] [LinearOrder V]
    (W X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hWX : forall u v, W.Adj u v -> X.Adj u v)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, W.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V)
    (f : Nat)
    (hEuler : (Fintype.card V : Int) - (X.edgeSet.ncard : Int) + (f : Int) = 2) :
    (3 : Int) * (f : Int) = 2 * (X.edgeSet.ncard : Int) := by sorry
