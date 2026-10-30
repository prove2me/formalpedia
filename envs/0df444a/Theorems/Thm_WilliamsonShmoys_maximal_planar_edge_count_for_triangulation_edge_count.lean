-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:34:04.868026+00:00
-- url     : https://prove2.me/theorems/2b15add2-440e-48d5-9af2-89aabca4d9f0
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal graph with a planar drawing and at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_edge_count {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = L) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
