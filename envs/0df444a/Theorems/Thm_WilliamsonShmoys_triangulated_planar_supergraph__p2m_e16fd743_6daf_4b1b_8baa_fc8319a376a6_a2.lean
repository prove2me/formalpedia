-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_planar_supergraph__p2m_e16fd743_6daf_4b1b_8baa_fc8319a376a6_a2
-- name    : WilliamsonShmoys.triangulated_planar_supergraph__p2m_e16fd743_6daf_4b1b_8baa_fc8319a376a6_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:02.431767+00:00
-- url     : https://prove2.me/theorems/ebb4e414-4dfa-4f3a-826b-c9f7b30cda57
-- title:
--   Triangulated planar supergraph on the same vertices
-- statement:
--   Every finite simple graph with a planar drawing and at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges. This captures the augmentation-to-triangulation and edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.triangulated_planar_supergraph__p2m_e16fd743_6daf_4b1b_8baa_fc8319a376a6_a2 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
