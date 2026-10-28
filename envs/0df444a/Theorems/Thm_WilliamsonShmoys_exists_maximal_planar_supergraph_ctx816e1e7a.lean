-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_ctx816e1e7a
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_ctx816e1e7a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:56:14.236903+00:00
-- url     : https://prove2.me/theorems/550b9175-8b2f-45c1-94d6-ca3b669c0d07
-- title:
--   Every planar graph has a maximal planar supergraph
-- statement:
--   Every planar graph on a finite vertex type is contained in an inclusion-maximal planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_ctx816e1e7a
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ U : SimpleGraph V, W < U → ¬ WilliamsonShmoys.HasPlanarDrawingOn U := by sorry
