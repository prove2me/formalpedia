-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_for_face_data
-- name    : WilliamsonShmoys.planar_drawing_euler_formula_for_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:35:55.904989+00:00
-- url     : https://prove2.me/theorems/037078b5-9cc7-4e00-bbae-af2e97dd7744
-- title:
--   Euler formula for connected planar drawing face data
-- statement:
--   A connected finite graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_formula_for_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    exists f : Nat, Fintype.card V + f = J.edgeSet.ncard + 2 := by sorry
