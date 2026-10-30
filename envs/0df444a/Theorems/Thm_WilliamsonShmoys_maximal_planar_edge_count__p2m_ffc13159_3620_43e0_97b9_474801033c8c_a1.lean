-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:12.622991+00:00
-- url     : https://prove2.me/theorems/af1e49eb-be12-4828-9ecb-8639ecce9cdd
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on those vertices has exactly 3n−6 edges. Maximality forces the drawing to be connected with triangular faces; Euler’s formula then gives the count, with the three-vertex case yielding the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
