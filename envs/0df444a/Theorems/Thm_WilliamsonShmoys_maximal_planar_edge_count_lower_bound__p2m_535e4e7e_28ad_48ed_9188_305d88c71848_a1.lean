-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:03:04.961037+00:00
-- url     : https://prove2.me/theorems/3b189e66-afee-4feb-9bd4-e20d54522d03
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V| − 6 edges; maximality forces a triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V ≤ L.edgeFinset.card + 6 := by sorry
