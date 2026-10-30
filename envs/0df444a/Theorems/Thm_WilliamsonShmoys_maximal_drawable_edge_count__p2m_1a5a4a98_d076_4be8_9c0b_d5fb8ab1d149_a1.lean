-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:06:40.271879+00:00
-- url     : https://prove2.me/theorems/646b5b89-5112-4cc7-9d4e-a59724ef3107
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ P : SimpleGraph V,
      N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
