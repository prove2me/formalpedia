-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_incidence_bound_edge_bound_fd674c06_a657_4ca8_b75f_41f75c897817
-- name    : WilliamsonShmoys.planar_face_incidence_bound_edge_bound_fd674c06_a657_4ca8_b75f_41f75c897817
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:49:26.227974+00:00
-- url     : https://prove2.me/theorems/efdb65a9-ed38-4865-8858-defaa2f32f6b
-- title:
--   Simple planar edge bound for the face incidence theorem
-- statement:
--   A connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3|V| − 6 edges. One proof route is to count directed edge sides along face-boundary walks, counting both sides of every bridge, and combine the lower bound of three sides per face with Euler’s formula. This edge bound and the target’s Euler equation imply the target by arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_incidence_bound_edge_bound_fd674c06_a657_4ca8_b75f_41f75c897817
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
