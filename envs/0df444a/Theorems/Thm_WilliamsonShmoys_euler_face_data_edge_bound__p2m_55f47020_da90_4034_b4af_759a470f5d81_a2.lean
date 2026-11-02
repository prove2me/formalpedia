-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_data_edge_bound__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
-- name    : WilliamsonShmoys.euler_face_data_edge_bound__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:52:20.71428+00:00
-- url     : https://prove2.me/theorems/f5fc13ff-ba54-4918-addb-9cedbc6aeaf9
-- title:
--   Count edges from Euler face data
-- statement:
--   Given face data satisfying Euler’s equation, the two-incidences-per-edge equation, and a lower bound of three on every face boundary, prove the planar edge bound. Sum the per-face lower bounds, substitute the incidence and Euler equations, then use the vertex lower bound to convert the result to the natural-number subtraction bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_data_edge_bound__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
    {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (faceCount : Nat)
    (boundaryLength : Fin faceCount → Nat)
    (hEuler : faceCount + Fintype.card V = G.edgeFinset.card + 2)
    (hIncidence : (∑ f : Fin faceCount, boundaryLength f) = 2 * G.edgeFinset.card)
    (hLength : ∀ f, 3 ≤ boundaryLength f)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
