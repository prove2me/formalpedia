-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:00:04.065183+00:00
-- url     : https://prove2.me/theorems/b2f3995c-fe31-4b09-a1d5-6579f9a9dbd9
-- title:
--   Finite maximal planar supergraph exists
-- statement:
--   Every graph admitting a drawing on a finite ordered vertex type has a drawable supergraph on that same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
