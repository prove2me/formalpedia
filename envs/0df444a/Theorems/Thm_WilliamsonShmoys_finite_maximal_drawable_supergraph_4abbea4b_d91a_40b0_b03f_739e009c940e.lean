-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_4abbea4b_d91a_40b0_b03f_739e009c940e
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph_4abbea4b_d91a_40b0_b03f_739e009c940e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:06:56.458098+00:00
-- url     : https://prove2.me/theorems/81de3adb-fd87-470d-9fbb-4ccd26daeb62
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   On a fixed finite vertex type, every drawable graph has a drawable supergraph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph_4abbea4b_d91a_40b0_b03f_739e009c940e
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ P : SimpleGraph V, M ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by sorry
