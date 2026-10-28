-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:27:20.05905+00:00
-- url     : https://prove2.me/theorems/5b5e2c80-4c9c-4575-869b-2e07197ac837
-- title:
--   Maximality forces the planar edge count lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
