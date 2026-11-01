-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:34.583113+00:00
-- url     : https://prove2.me/theorems/3c202fe3-e8d7-442a-bae3-52d08143dac3
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A drawable simple graph with at least three vertices that is maximal under drawable supergraphs has at least 3|V| − 6 edges. Extend its drawing to a triangulation on the same vertex set; maximality forces the extension to equal the original graph, and Euler’s formula gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by sorry
