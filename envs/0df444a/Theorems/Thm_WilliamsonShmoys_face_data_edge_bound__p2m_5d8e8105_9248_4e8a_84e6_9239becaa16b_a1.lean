-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_edge_bound__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
-- name    : WilliamsonShmoys.face_data_edge_bound__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:10.406657+00:00
-- url     : https://prove2.me/theorems/d86bd1dd-f34d-4327-8a91-73c00da45b5e
-- title:
--   Derive the planar edge bound from face data
-- statement:
--   Euler’s relation and the face-boundary inequalities imply the simple planar edge bound. This is a natural-number arithmetic step: substitute the total boundary length and Euler relation, then rearrange the resulting linear inequalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.face_data_edge_bound__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (F B : ℕ)
    (hEuler : Fintype.card V + F = K.edgeFinset.card + 2)
    (hBoundaryLower : 3 * F ≤ B)
    (hBoundaryCount : B = 2 * K.edgeFinset.card) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
