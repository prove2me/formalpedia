-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_ctx816e1e7
-- name    : WilliamsonShmoys.maximal_planar_supergraph_ctx816e1e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:46:52.593987+00:00
-- url     : https://prove2.me/theorems/bdfa1f2d-639e-4ba9-8934-b3212f4b6f96
-- title:
--   A maximal drawable supergraph exists
-- statement:
--   Every drawable graph on the fixed finite vertex type is contained in a drawable supergraph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ Q : SimpleGraph V,
      W ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by sorry
