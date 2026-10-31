-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:53.437051+00:00
-- url     : https://prove2.me/theorems/c23ffc9b-3ccd-4354-ad9d-982ada7aecad
-- title:
--   Count the edges of a maximal drawable planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
