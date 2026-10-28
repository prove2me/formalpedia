-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_completion_cardinality_maximal_exists
-- name    : WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:39:58.620355+00:00
-- url     : https://prove2.me/theorems/b0e490f3-600c-41dd-a366-4a4046be4c05
-- title:
--   A maximal drawable supergraph exists
-- statement:
--   Every drawable graph on the given finite vertex type has a drawable supergraph that admits no strictly larger drawable supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        ∀ U : SimpleGraph V,
          W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W := by sorry
