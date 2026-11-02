-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_certificate_edge_bound__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
-- name    : WilliamsonShmoys.planar_face_count_certificate_edge_bound__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:49.659019+00:00
-- url     : https://prove2.me/theorems/5f2364e6-6a88-491d-a1f1-2c57e752bc78
-- title:
--   Edge bound from Euler and face incidence counts
-- statement:
--   The Euler and triangular incidence equations imply the requested edge lower bound for at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_certificate_edge_bound__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (F : ℕ) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    (Fintype.card V + F = P.edgeFinset.card + 2) ->
    (3 * F = 2 * P.edgeFinset.card) ->
    (3 <= Fintype.card V) ->
    3 * Fintype.card V - 6 <= P.edgeFinset.card := by sorry
