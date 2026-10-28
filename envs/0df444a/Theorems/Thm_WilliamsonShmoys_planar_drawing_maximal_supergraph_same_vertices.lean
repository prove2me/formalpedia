-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_same_vertices
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:40:53.913881+00:00
-- url     : https://prove2.me/theorems/baf13dd3-b6ab-4e4a-95f9-ebfa7a0ad84c
-- title:
--   Maximal drawn supergraph on the same vertices
-- statement:
--   Any finite drawn graph on at least three vertices has an inclusion-maximal drawn supergraph on the same vertices, with no fewer edges. This separates the finite maximization step from the topological edge-count argument. Maximize edge count among drawn supergraphs of X; the drawing remains valid when edges are removed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      X ≤ H ∧
      (X.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K = H) := by
  sorry
