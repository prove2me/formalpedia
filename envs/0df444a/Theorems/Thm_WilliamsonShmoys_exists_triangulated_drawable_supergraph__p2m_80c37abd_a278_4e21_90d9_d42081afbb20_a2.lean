-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph__p2m_80c37abd_a278_4e21_90d9_d42081afbb20_a2
-- name    : WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_80c37abd_a278_4e21_90d9_d42081afbb20_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:57.704196+00:00
-- url     : https://prove2.me/theorems/d83565dc-e27f-4a43-b95a-82c38890bb42
-- title:
--   Augmenting a planar drawing to the triangulation edge count
-- statement:
--   Given a crossing-free drawing on a finite linearly ordered vertex type with at least three vertices, there is a drawable supergraph on the same vertices whose edge count is 3|V|−6, and the original graph has no more edges than that supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_80c37abd_a278_4e21_90d9_d42081afbb20_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hR : HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      HasPlanarDrawingOn S ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       letI : DecidableRel S.Adj := Classical.decRel S.Adj
       R.edgeFinset.card ≤ S.edgeFinset.card ∧
       S.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
