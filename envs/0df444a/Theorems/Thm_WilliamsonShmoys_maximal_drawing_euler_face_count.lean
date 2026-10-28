-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_euler_face_count
-- name    : WilliamsonShmoys.maximal_drawing_euler_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:31:41.047452+00:00
-- url     : https://prove2.me/theorems/0175589f-c958-49a1-a73d-93f23477c1eb
-- title:
--   Euler and face-incidence certificate for maximal drawable graphs
-- statement:
--   A maximal drawable simple graph on at least three vertices has a face count satisfying the connected Euler equation and the triangular face-incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall H : SimpleGraph V, G <= H ->
      WilliamsonShmoys.HasPlanarDrawingOn H -> H <= G)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by sorry
