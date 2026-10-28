-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_20261026
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:37:33.305857+00:00
-- url     : https://prove2.me/theorems/f70cb8ba-c400-49d8-af47-47d0ba53a717
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every finite graph with the specified planar drawing has a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  sorry
