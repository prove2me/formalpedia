-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_extension_for_edge_bound
-- name    : WilliamsonShmoys.planar_drawingOn_triangulation_extension_for_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:51:34.447877+00:00
-- url     : https://prove2.me/theorems/acf4f5e7-beb2-4e5a-aef7-83dd7a2b75aa
-- title:
--   Triangulation extension for a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices extends, on the same vertex set, to a drawable triangulation whose edge count satisfies |E| + 6 = 3|V|. This supplies the topological augmentation and Euler-counting step for the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_triangulation_extension_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
