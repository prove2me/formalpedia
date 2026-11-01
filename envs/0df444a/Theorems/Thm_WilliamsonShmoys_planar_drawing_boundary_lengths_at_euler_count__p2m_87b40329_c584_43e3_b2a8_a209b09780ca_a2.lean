-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
-- name    : WilliamsonShmoys.planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:37.986362+00:00
-- url     : https://prove2.me/theorems/5616da3e-b404-43c0-825c-d8d997481a46
-- title:
--   Facial boundary lengths at an Euler face count
-- statement:
--   At any natural face count satisfying Euler’s equation, enumerate facial boundary walks so their lengths sum to twice the edge count and every walk has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (faceCount : Nat)
    (hEuler : Fintype.card V + faceCount = K.edgeFinset.card + 2) :
    ∃ boundaryLength : Fin faceCount → Nat,
      (∑ f : Fin faceCount, boundaryLength f) = 2 * K.edgeFinset.card ∧
      (∀ f : Fin faceCount, 3 ≤ boundaryLength f) := by
  sorry
