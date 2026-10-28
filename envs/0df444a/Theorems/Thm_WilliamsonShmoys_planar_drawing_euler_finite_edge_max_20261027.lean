-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_finite_edge_max_20261027
-- name    : WilliamsonShmoys.planar_drawing_euler_finite_edge_max_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:45:28.65399+00:00
-- url     : https://prove2.me/theorems/0de80f5b-18fb-43b4-98a2-baff59f2dfd5
-- title:
--   Maximum-edge drawable supergraph on a finite vertex type
-- statement:
--   On a finite ordered vertex type, a drawable graph has a drawable supergraph whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_finite_edge_max_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        K ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
