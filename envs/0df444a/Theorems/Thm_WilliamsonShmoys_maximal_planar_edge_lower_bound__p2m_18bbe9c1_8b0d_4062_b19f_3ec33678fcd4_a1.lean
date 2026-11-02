-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:53.836883+00:00
-- url     : https://prove2.me/theorems/2d3bff7d-8a6a-45d8-b748-fea14c5aa101
-- title:
--   Maximal drawable graphs have at least 3n−6 edges
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by sorry
