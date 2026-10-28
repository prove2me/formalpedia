-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_drawing_edge_bound
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_drawing_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:43:59.432989+00:00
-- url     : https://prove2.me/theorems/763c612a-64b1-4d02-893f-b499164299a0
-- title:
--   Choose a maximal planar supergraph for the drawing edge bound
-- statement:
--   Among the planar drawing supergraphs of M on the same finite vertex type, choose one maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMdraw : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet := by sorry
