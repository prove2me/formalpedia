-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_graph_has_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawable_graph_has_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:42:10.779784+00:00
-- url     : https://prove2.me/theorems/871e00b6-91bf-41ea-9957-2907cb9e0dc1
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   Any finite graph with a drawing satisfying HasPlanarDrawingOn is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_graph_has_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      S ≤ R ∧
      ∀ T : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn T →
        R ≤ T → T = R := by sorry
