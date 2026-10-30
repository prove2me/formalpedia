-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangular_edge_count
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:10:57.139987+00:00
-- url     : https://prove2.me/theorems/e20a9b21-2bfd-4446-a4dd-6a64e939359c
-- title:
--   Every finite planar drawing extends to a graph with the triangular edge count
-- statement:
--   For any finite graph with a crossing-free drawing and at least three vertices, there is a drawable supergraph on the same vertex type whose edge count is 3|V|−6. The case of exactly three vertices is included; the graph need not be connected. Prove this by extending a drawing to a triangulation, then applying Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
