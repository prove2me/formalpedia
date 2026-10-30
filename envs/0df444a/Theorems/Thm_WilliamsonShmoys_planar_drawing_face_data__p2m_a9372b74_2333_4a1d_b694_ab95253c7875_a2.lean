-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T19:52:20.596006+00:00
-- url     : https://prove2.me/theorems/997243ae-8756-4ede-bc08-017e56f3a3d3
-- title:
--   Extract finite face data from a connected planar drawing
-- statement:
--   For a connected finite simple graph with at least three vertices and a crossing-free drawing, construct finite face data satisfying Euler's formula, the two-sided edge-incidence count, and the lower bound of three on each face boundary. The independent proof route is to extract cyclic orders from the drawing, define faces via the induced permutation on directed edge ends, and establish the planar Euler characteristic and face-length bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    Nonempty (WilliamsonShmoys.PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K) := by sorry
