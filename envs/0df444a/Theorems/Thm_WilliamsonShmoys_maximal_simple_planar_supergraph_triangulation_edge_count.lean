-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_simple_planar_supergraph_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_simple_planar_supergraph_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:59:11.311226+00:00
-- url     : https://prove2.me/theorems/21353b1d-4163-4523-81fd-5dde183dfe4f
-- title:
--   Edge count of a maximal simple planar graph
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices, maximal among planar supergraphs on those vertices, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_simple_planar_supergraph_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
