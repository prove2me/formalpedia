-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:26.65225+00:00
-- url     : https://prove2.me/theorems/edf71842-1b5c-4584-b66a-8a3d7af33e5d
-- title:
--   Edge bound for maximal planar drawings
-- statement:
--   A maximal planar simple graph on at least three vertices has at most three times the number of vertices minus six edges, expressed without truncated subtraction. The proof route is to obtain a plane embedding with triangular faces, apply Euler’s formula and count edge-face incidences; the continuous-arc drawing predicate still needs to be connected to that face-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     2 * G.edgeFinset.card + 12 ≤ 6 * Fintype.card V) := by sorry
