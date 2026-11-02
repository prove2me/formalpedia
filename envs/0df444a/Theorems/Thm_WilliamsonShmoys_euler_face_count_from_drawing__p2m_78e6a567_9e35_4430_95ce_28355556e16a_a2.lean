-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
-- name    : WilliamsonShmoys_euler_face_count_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:22:29.457093+00:00
-- url     : https://prove2.me/theorems/d20d18a3-5a54-4383-a267-bcf89dfad85c
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   Every finite connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula. The drawing yields a finite rotation system; its face cycles and the Euler characteristic of the connected embedded graph provide a proof route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys_euler_face_count_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + (f : ℤ) = 2 := by
  sorry
