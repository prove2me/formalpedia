-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
-- name    : WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:19.029985+00:00
-- url     : https://prove2.me/theorems/89410822-d74b-4a7e-a2fa-750ec8304b72
-- title:
--   Face-count certificate for a connected planar drawing
-- statement:
--   A crossing-free drawing of a finite connected simple graph with at least three vertices yields a finite collection of face boundary lengths. Their count satisfies Euler’s relation, their total is twice the edge count, and every length is at least three. Prove this by extracting a rotation system from the drawing, defining faces from the permutation on directed edge ends, and proving Euler’s formula and the incidence count. Connectedness and the vertex lower bound are needed to rule out facial boundary walks of length one or two, including in the presence of bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (f : ℕ) (length : Fin f → ℕ),
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
      2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) =
        ∑ i, length i ∧
      ∀ i, 3 ≤ length i := by sorry
