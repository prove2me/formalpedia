-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_59c448d8_2415_4b81_b96a_4b978426d513_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_59c448d8_2415_4b81_b96a_4b978426d513_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:43:39.283828+00:00
-- url     : https://prove2.me/theorems/61d32ba8-63e6-4051-9eef-c43df50e222b
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_59c448d8_2415_4b81_b96a_4b978426d513_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
