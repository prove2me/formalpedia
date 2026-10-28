-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_supergraph_completion
-- name    : WilliamsonShmoys.planar_graph_has_dense_supergraph_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:24:59.886014+00:00
-- url     : https://prove2.me/theorems/932ee8f7-1f4c-44d2-9f10-3199153b8220
-- title:
--   Dense planar supergraph completion
-- statement:
--   Every drawable graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly $3|V|-6$ edges. This isolates planar augmentation and the triangulation/Euler argument from the parent’s maximality application. An independent route is to extend the drawing by drawable edges until no further edge can be added, prove that every face is triangular, and apply Euler’s formula. The main remaining work is to formalize edge insertion and the face argument for the predicate’s arc-based drawing representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_dense_supergraph_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
