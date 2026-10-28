-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_exact_edge_count__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_has_exact_edge_count__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:57:11.43198+00:00
-- url     : https://prove2.me/theorems/7a2d1b0a-59f6-4246-bb02-8a4c93f926fa
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   If L is drawable, contains K, and has at least as many edges as every drawable supergraph of K, then for at least three vertices L has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_has_exact_edge_count__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hKL : K ≤ L)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
