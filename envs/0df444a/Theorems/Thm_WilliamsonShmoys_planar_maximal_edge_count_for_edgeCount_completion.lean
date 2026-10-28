-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_for_edgeCount_completion
-- name    : WilliamsonShmoys.planar_maximal_edge_count_for_edgeCount_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:03:26.722992+00:00
-- url     : https://prove2.me/theorems/07534bdd-cb73-4c15-8caa-5b8e1dc6ae8d
-- title:
--   An edge-maximal planar graph has the triangulation edge count
-- statement:
--   An edge-maximal graph satisfying the given crossing-free drawing predicate, on at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count_for_edgeCount_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion W W)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
