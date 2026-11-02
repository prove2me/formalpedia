-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_counting_edge_bound__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
-- name    : WilliamsonShmoys.euler_face_counting_edge_bound__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:48:57.551187+00:00
-- url     : https://prove2.me/theorems/4153da1a-c310-463f-bd9f-67ae5572ba0b
-- title:
--   Euler face counting gives the planar edge bound
-- statement:
--   Given Euler’s relation, at least three darts per face, and an exact count of all darts among the faces, the dart count being twice the number of edges implies the planar edge bound when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_counting_edge_bound__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
    {V : Type} [Fintype V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (F : Type) [Fintype F] [DecidableEq F] (face : K.Dart → F)
    (hEuler : Fintype.card V + Fintype.card F = K.edgeFinset.card + 2)
    (hdeg : ∀ f : F, 3 ≤ Fintype.card {d : K.Dart // face d = f})
    (hcount : (∑ f : F, Fintype.card {d : K.Dart // face d = f}) = Fintype.card K.Dart)
    (hdart : Fintype.card K.Dart = 2 * K.edgeFinset.card)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
