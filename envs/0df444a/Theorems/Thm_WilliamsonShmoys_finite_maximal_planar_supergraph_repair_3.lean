-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph_repair_3
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph_repair_3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:40:49.140985+00:00
-- url     : https://prove2.me/theorems/d1c345fc-0479-4ddb-b4be-0f3eaf9617a5
-- title:
--   Existence of a maximal drawable supergraph on a finite vertex set
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_supergraph_repair_3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
