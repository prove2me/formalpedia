-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_graph_has_maximal_supergraph
-- name    : WilliamsonShmoys.finite_drawable_graph_has_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:04:24.370196+00:00
-- url     : https://prove2.me/theorems/4fbfa33a-425a-42fe-a1cf-4140d181d9d7
-- title:
--   A finite drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_drawable_graph_has_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
