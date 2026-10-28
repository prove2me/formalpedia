-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate_2026
-- name    : WilliamsonShmoys.maximal_planar_face_count_certificate_2026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:47:18.526673+00:00
-- url     : https://prove2.me/theorems/2d7eb523-8822-4c67-8c35-e76cd8f064be
-- title:
--   Euler and triangular-face count for a maximal planar drawing
-- statement:
--   For a finite graph with at least three vertices, a crossing-free arc drawing, and no strictly larger drawable graph on the same vertices, there is a natural number of faces f such that Euler’s equation |V| + f = |E| + 2 and triangular-face incidence 3f = 2|E| both hold. The lower bound excludes smaller maximal graphs where the target edge formula fails.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_count_certificate_2026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall H : SimpleGraph V, K <= H -> HasPlanarDrawingOn H -> H = K) :
    Exists fun f : Nat =>
      Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f = 2 * K.edgeSet.ncard := by sorry
