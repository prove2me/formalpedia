-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_certificate__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
-- name    : WilliamsonShmoys.planar_face_count_certificate__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:13.609207+00:00
-- url     : https://prove2.me/theorems/2f467046-6ecc-4acc-90cd-01be23afbfca
-- title:
--   Euler and face-incidence certificate for a planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there are finitely many facial boundary walks whose count satisfies Euler’s formula, whose total length counts every edge twice, and each of whose lengths is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_certificate__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (F : Nat) (faceLength : Fin F → Nat),
      Fintype.card V + F = K.edgeFinset.card + 2 ∧
      (∑ i : Fin F, faceLength i) = 2 * K.edgeFinset.card ∧
      ∀ i, 3 ≤ faceLength i := by sorry
