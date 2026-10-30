-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_has_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_planar_has_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:57:02.389691+00:00
-- url     : https://prove2.me/theorems/89f99499-2712-4a23-a5c2-36fa62fde7e2
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges. The key work is showing the drawing of a maximal graph has triangular faces and applying Euler’s formula, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_has_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
