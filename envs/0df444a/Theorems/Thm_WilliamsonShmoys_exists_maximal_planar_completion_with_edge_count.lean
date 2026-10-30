-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_with_edge_count
-- name    : WilliamsonShmoys.exists_maximal_planar_completion_with_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:40:05.181208+00:00
-- url     : https://prove2.me/theorems/c5bfb3bb-c124-4a2c-be08-3e9d3c0f1416
-- title:
--   Complete a planar drawing to a triangulation on the same vertices
-- statement:
--   Every graph with a drawing as defined in the imported module, on at least three vertices, has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_completion_with_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 <= Fintype.card V) :
    ∃ Y : SimpleGraph V,
      LE.le X Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
