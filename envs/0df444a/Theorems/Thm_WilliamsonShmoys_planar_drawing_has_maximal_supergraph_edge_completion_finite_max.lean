-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_edge_completion_finite_max
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_edge_completion_finite_max
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:24:44.83246+00:00
-- url     : https://prove2.me/theorems/e9147cdc-f87e-49e7-88a8-b4f6b6f8a338
-- title:
--   Maximal planar completion by finite edge maximization
-- statement:
--   A graph with a planar drawing has an inclusion-maximal planar supergraph on the same finite ordered vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_edge_completion_finite_max
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion W X := by sorry
