-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_maximal_extension__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
-- name    : WilliamsonShmoys.finite_drawable_maximal_extension__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:33.073375+00:00
-- url     : https://prove2.me/theorems/0117d7a7-55cc-4763-b339-05a114946f12
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_drawable_maximal_extension__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
