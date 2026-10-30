-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_completion
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_for_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:08:48.341521+00:00
-- url     : https://prove2.me/theorems/c020a901-1ff9-4a03-b7c6-f18f1d2c2fb4
-- title:
--   A maximal planar graph with at least three vertices has the planar edge count
-- statement:
--   A graph maximal among planar supergraphs on its finite vertex type has exactly three times its vertex count minus six edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_for_completion {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : HasPlanarDrawingOn K) (hMaximal : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
