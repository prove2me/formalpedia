-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_candidate
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:49:55.571555+00:00
-- url     : https://prove2.me/theorems/397071d2-54cd-4807-97e7-b4001b0535bd
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This stronger completion result handles disconnected starting graphs as well; with three vertices the completion is the triangle. Its proof requires extending a drawing to a maximal planar supergraph and formalizing the triangular-face and Euler-count argument. The parent uses maximality to identify this extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
