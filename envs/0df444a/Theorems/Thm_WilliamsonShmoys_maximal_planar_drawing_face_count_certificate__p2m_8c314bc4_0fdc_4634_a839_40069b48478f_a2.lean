-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:27.597831+00:00
-- url     : https://prove2.me/theorems/e876f463-155f-4870-984e-4729243320c4
-- title:
--   Euler and incidence counts for a maximal planar drawing
-- statement:
--   For a drawable graph maximal among drawable supergraphs on the same vertices, with at least three vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v : V}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q ->
      (forall {u v : V}, Q.Adj u v -> P.Adj u v)) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    Exists fun F : ℕ =>
      Fintype.card V + F = P.edgeFinset.card + 2 ∧
      3 * F = 2 * P.edgeFinset.card := by sorry
