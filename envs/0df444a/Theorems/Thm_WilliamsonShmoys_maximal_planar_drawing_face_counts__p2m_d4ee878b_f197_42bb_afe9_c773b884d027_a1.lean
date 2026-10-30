-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_counts__p2m_d4ee878b_f197_42bb_afe9_c773b884d027_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_d4ee878b_f197_42bb_afe9_c773b884d027_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:15.444791+00:00
-- url     : https://prove2.me/theorems/5172cebe-7d77-4b25-aa7c-10802cca0895
-- title:
--   Euler and triangular-face counts for a maximal planar drawing
-- statement:
--   A maximal planar drawing on at least three vertices has a face count f satisfying Euler’s relation |V| + f = |E| + 2 and the triangular-face incidence count 2|E| = 3f. Prove this by extracting the planar embedding and its faces from the drawing, using maximality to obtain connectedness and triangular faces, and counting edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_d4ee878b_f197_42bb_afe9_c773b884d027_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      2 * H.edgeFinset.card = 3 * f := by
  sorry
