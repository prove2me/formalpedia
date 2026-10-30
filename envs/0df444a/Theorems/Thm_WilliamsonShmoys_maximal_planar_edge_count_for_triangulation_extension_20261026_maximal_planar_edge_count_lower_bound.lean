-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:58:53.494238+00:00
-- url     : https://prove2.me/theorems/e8404987-fef7-4615-812d-47ea2c9e93da
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   An edge-maximal simple graph admitting a crossing-free drawing on at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
