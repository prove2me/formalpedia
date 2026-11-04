-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:00.76956+00:00
-- url     : https://prove2.me/theorems/b664cddc-4710-40ab-ab7d-a96b7cb12f1c
-- title:
--   Face count and boundary lengths from a planar drawing
-- statement:
--   A finite connected simple graph on at least three vertices with the specified crossing-free drawing has a number of faces satisfying Euler’s formula and the bound that total face-boundary length is at most twice the number of edges. The drawing-to-plane-embedding and face-boundary argument is the remaining topological core.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * K.edgeFinset.card := by sorry
