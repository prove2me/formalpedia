-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_maximal_planar_drawing
-- name    : WilliamsonShmoys.planar_edge_bound_of_maximal_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:33:25.911107+00:00
-- url     : https://prove2.me/theorems/f21dd46e-700f-470f-a2af-d60ee069f312
-- title:
--   Euler edge bound for a maximal planar drawing
-- statement:
--   An inclusion-maximal planar graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_of_maximal_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
