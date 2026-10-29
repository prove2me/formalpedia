-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:41:01.674983+00:00
-- url     : https://prove2.me/theorems/f852174d-ad4f-4de3-989a-32d5dda8e860
-- title:
--   Planar graphs admit a triangulation completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This is a reusable planar augmentation theorem: add noncrossing edges within faces until every face is triangular, then apply Euler’s formula. It removes the geometric completion and edge-count work from the parent. The parent applies its maximality hypothesis to the resulting supergraph and concludes it equals K. The child’s independent proof must formalize the passage from the supplied curve drawing to face augmentation and the triangulation count; the hypotheses retain the required vertex lower bound and preserve the original vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
