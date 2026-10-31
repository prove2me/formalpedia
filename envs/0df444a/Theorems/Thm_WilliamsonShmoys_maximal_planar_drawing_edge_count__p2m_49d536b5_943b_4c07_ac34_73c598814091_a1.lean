-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:57.524993+00:00
-- url     : https://prove2.me/theorems/77b00c13-46d0-475b-a33c-447ffd078949
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that has no strictly larger drawable supergraph on the same vertices has the maximal planar edge count. This includes the three-vertex case, where the maximal graph is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
