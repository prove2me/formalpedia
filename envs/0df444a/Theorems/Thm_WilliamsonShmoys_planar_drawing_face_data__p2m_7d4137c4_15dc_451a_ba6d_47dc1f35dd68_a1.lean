-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:14:08.203853+00:00
-- url     : https://prove2.me/theorems/fe05758f-8425-4cd3-8700-8a0a027cbbe8
-- title:
--   Euler and face-boundary data from a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the specified crossing-free drawing has a finite collection of face boundary lengths whose count satisfies Euler’s equation, whose total is twice the number of edges, and each of which is at least three. The size hypothesis excludes the connected one-edge case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (f : ℕ) (boundary : Fin f → ℕ),
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      (∑ i : Fin f, boundary i) = 2 * K.edgeSet.ncard ∧
      ∀ i, 3 ≤ boundary i := by sorry
