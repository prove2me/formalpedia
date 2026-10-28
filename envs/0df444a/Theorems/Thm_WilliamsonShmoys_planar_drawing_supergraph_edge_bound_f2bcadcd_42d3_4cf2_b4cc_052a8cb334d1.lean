-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_bound_f2bcadcd_42d3_4cf2_b4cc_052a8cb334d1
-- name    : WilliamsonShmoys.planar_drawing_supergraph_edge_bound_f2bcadcd_42d3_4cf2_b4cc_052a8cb334d1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:37:51.525434+00:00
-- url     : https://prove2.me/theorems/6daa1fb6-f812-4cda-9b89-dcc27e08a5f0
-- title:
--   A drawable supergraph reaches the planar edge bound
-- statement:
--   Every drawable simple graph on a fixed finite vertex type with at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges. A proof route chooses an edge-maximal drawable supergraph among the finitely many graphs on that vertex type, then proves the classical maximal-planar edge bound using the necessary embedding structure and Euler’s formula. The hypothesis covers the three-vertex boundary case. This is a substantial proof obligation, not a sourced established lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_supergraph_edge_bound_f2bcadcd_42d3_4cf2_b4cc_052a8cb334d1
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    ∃ Y : SimpleGraph V, HasPlanarDrawingOn Y ∧
      (∀ u v, X.Adj u v → Y.Adj u v) ∧
      3 * (Fintype.card V : Int) - 6 <= (Y.edgeSet.ncard : Int) := by sorry
