-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:32:12.83919+00:00
-- url     : https://prove2.me/theorems/536ad4cb-c7a2-4d05-ba35-c09e88fe58c7
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph maximal under the specified planar drawing predicate has exactly three times its vertex count minus six edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
