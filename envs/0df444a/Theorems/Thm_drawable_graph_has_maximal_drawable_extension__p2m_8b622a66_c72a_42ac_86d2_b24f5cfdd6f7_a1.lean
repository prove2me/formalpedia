-- Prove2me | Theorems.Thm_drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
-- name    : drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:29.016209+00:00
-- url     : https://prove2.me/theorems/12591a48-153c-4bb8-a571-e0af3ea72a75
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K := by
  sorry
