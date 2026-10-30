-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count_acab26a7
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count_acab26a7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:22:56.703862+00:00
-- url     : https://prove2.me/theorems/a305a22a-04de-49be-9799-99d7d62ec7c8
-- title:
--   Planar graphs admit a triangulated supergraph
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable simple graph on the same vertices with exactly 3|V| − 6 edges. This isolates the geometric completion and Euler-counting work; the parent uses maximality to identify the completion with H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count_acab26a7
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
