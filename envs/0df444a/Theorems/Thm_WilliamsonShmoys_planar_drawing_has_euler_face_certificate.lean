-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_certificate
-- name    : WilliamsonShmoys.planar_drawing_has_euler_face_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:36:30.230816+00:00
-- url     : https://prove2.me/theorems/a1e2d0d8-f449-43f5-a2aa-3b35e98ff6f4
-- title:
--   Euler face certificate from a planar drawing
-- statement:
--   For a finite connected simple graph on at least three ordered vertices, a crossing-free drawing yields a number of faces satisfying Euler’s equation and the total face-boundary-length lower bound. This removes the topological argument from the target; a proof route is to form the plane embedding from the drawing, use connectedness for Euler’s formula, and count edge-sides around faces, using simplicity and at least three vertices to rule out faces of length below three. Small cases and the hypotheses must be checked when formalizing those face counts. This is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_euler_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      (Fintype.card V : Int) - (H.edgeSet.ncard : Int) + (f : Int) = 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by sorry
