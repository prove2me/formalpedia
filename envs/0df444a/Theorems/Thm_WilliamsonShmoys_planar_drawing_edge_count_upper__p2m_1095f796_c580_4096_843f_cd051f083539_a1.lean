-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:19.587986+00:00
-- url     : https://prove2.me/theorems/7a1738f6-5642-467f-b376-eb6ed4a76310
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every graph with the supplied crossing-free drawing on at least three vertices has at most $3|V|-6$ edges. This is a standard planar edge bound, independent of maximality. A proof route is to extend the drawing to a maximal planar drawing on the same vertex set, then use Euler's formula and count each triangular face boundary edge twice. The lower bound on the vertex count is needed for the subtraction and the face-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
