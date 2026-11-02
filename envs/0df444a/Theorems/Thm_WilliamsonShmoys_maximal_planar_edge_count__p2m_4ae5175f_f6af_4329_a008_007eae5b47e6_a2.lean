-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:45:57.943266+00:00
-- url     : https://prove2.me/theorems/535e4e7e-28ad-48ed-9188-305d88c71848
-- title:
--   Exact edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
