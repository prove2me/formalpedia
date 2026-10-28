-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_supergraph_repair
-- name    : WilliamsonShmoys.planar_completion_exists_maximal_supergraph_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:53:42.956985+00:00
-- url     : https://prove2.me/theorems/83796c88-40a9-4105-a628-85d796a45800
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in an inclusion-maximal drawable supergraph on that same type. The given drawing makes the finite collection of eligible supergraphs nonempty; a maximal element of that collection has the stated property. No vertex-count lower bound is needed for this existence step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_exists_maximal_supergraph_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        ∀ U : SimpleGraph V,
          W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W := by sorry
