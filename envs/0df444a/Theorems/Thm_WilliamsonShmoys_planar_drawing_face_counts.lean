-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_counts
-- name    : WilliamsonShmoys.planar_drawing_face_counts
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T00:52:37.570224+00:00
-- url     : https://prove2.me/theorems/93758648-201b-4536-99fe-49cf854de3d2
-- title:
--   Euler and facial incidence counts for a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has a finite number f of faces satisfying Euler’s formula |V| + f = |E| + 2 and the facial edge-side bound 2|E| ≤ 3f.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_counts
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      2 * H.edgeSet.ncard ≤ 3 * f := by sorry
