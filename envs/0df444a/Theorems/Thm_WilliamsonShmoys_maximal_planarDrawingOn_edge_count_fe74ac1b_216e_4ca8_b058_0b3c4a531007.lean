-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_count_fe74ac1b_216e_4ca8_b058_0b3c4a531007
-- name    : WilliamsonShmoys.maximal_planarDrawingOn_edge_count_fe74ac1b_216e_4ca8_b058_0b3c4a531007
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:55:46.719997+00:00
-- url     : https://prove2.me/theorems/d50d73e2-914c-4c79-8582-24c0dc335bdf
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no proper drawable supergraph on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planarDrawingOn_edge_count_fe74ac1b_216e_4ca8_b058_0b3c4a531007
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
