-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_maximal
-- name    : WilliamsonShmoys.planar_drawable_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:11:14.676949+00:00
-- url     : https://prove2.me/theorems/20a62ee0-9734-459d-bd73-0d8768f42695
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph on that same type whose edge count is maximal among drawable supergraphs; the completion has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_supergraph_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ H : SimpleGraph V, Q ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Q.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
