-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count__p2m_15adcf76_f3b0_4eb0_a8d6_6562dc150ecb_a1
-- name    : WilliamsonShmoys.maximal_planar_face_count__p2m_15adcf76_f3b0_4eb0_a8d6_6562dc150ecb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:54:02.922447+00:00
-- url     : https://prove2.me/theorems/94636b31-2f9e-4256-93d0-7a9950cdcd71
-- title:
--   Euler and triangular-face count for a maximal planar drawing
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set, there is a face count satisfying Euler’s vertex-edge-face equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_count__p2m_15adcf76_f3b0_4eb0_a8d6_6562dc150ecb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f = 2 * H.edgeFinset.card := by
  sorry
