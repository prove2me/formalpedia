-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_d41641eb_86db_4b4e_b9d1_2259e7f78f1b
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_d41641eb_86db_4b4e_b9d1_2259e7f78f1b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:53:32.716475+00:00
-- url     : https://prove2.me/theorems/298b1a86-18b6-4bc5-96f4-b68905059bb9
-- title:
--   Planar triangulation completion with exact edge count
-- statement:
--   Every graph with the supplied planar drawing on a finite ordered vertex type of size at least three has a planar supergraph on the same vertex set with exactly `3|V| − 6` edges. This isolates the completion and Euler-count argument used by the parent. One proof route maximizes the number of edges among drawn planar supergraphs, adds edges across components and nontriangular faces until none can be added, then applies Euler’s formula and face-edge incidence counting. The boundary case of three vertices gives the three-edge triangle. Formalizing the topological completion for the exact continuous-arc predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_d41641eb_86db_4b4e_b9d1_2259e7f78f1b
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDrawing : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  sorry
