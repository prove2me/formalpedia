-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:11.803996+00:00
-- url     : https://prove2.me/theorems/306301a2-72f6-4d8f-a2c9-6046e69fec66
-- title:
--   Edge bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable connected simple graph on at least three vertices has at most `3|V| - 6` edges. The mathematical route is to interpret the drawing as a plane embedding; maximality then forces every face boundary to have length three. Euler’s formula and the fact that every edge is incident to two face sides give `3F = 2E` and `|V| - E + F = 2`, yielding `E = 3|V| - 6`. The exact arc-to-embedding and face-count formalization remains the central proof obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
