-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:28:13.746903+00:00
-- url     : https://prove2.me/theorems/36222aef-f651-4edc-b4ea-61d97c0a711e
-- title:
--   A drawable graph has an exact edge-count completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges. At |V|=3, this completion is the triangle. For larger sets, the completion is obtained by extending the drawing to a maximal planar graph and counting its triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
