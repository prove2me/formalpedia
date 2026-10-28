-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_on_fixed_vertices
-- name    : WilliamsonShmoys.maximal_planar_supergraph_on_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:32:36.599671+00:00
-- url     : https://prove2.me/theorems/aa78bdea-53ad-43f5-a6dd-2d460f5254a5
-- title:
--   Existence of a maximal drawable supergraph on a fixed vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that cannot be properly enlarged while preserving drawability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W := by
  sorry
