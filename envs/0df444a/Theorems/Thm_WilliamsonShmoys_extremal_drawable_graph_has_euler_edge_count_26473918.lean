-- Prove2me | Theorems.Thm_WilliamsonShmoys_extremal_drawable_graph_has_euler_edge_count_26473918
-- name    : WilliamsonShmoys.extremal_drawable_graph_has_euler_edge_count_26473918
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:49:23.877643+00:00
-- url     : https://prove2.me/theorems/39cb4e21-5e99-4085-b73c-5a5667f48d95
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has exactly three times the vertex count minus six edges. The independent proof route is to show maximality forces a connected triangulated plane embedding and apply Euler’s formula; the three-vertex case gives the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.extremal_drawable_graph_has_euler_edge_count_26473918
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hNmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
