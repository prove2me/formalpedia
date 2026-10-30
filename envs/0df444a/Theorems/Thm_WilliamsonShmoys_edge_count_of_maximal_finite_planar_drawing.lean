-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_finite_planar_drawing
-- name    : WilliamsonShmoys.edge_count_of_maximal_finite_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:16:11.731069+00:00
-- url     : https://prove2.me/theorems/c797896d-c5f4-44ff-a8ff-d1b689e5dd9a
-- title:
--   Edge count of a maximal finite planar drawing
-- statement:
--   A maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_finite_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
