-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count_for_triangulated_extension
-- name    : WilliamsonShmoys.maximal_planar_extension_edge_count_for_triangulated_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:14:06.157584+00:00
-- url     : https://prove2.me/theorems/dab1c322-eb27-4595-920f-b3e42afc5ffe
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable graphs has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_edge_count_for_triangulated_extension {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMaximal : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
