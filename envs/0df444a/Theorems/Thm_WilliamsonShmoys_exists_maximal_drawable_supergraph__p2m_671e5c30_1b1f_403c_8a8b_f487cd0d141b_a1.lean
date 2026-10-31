-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:12.818729+00:00
-- url     : https://prove2.me/theorems/9f3f57e7-072a-48ca-8b31-876be4b03c90
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
