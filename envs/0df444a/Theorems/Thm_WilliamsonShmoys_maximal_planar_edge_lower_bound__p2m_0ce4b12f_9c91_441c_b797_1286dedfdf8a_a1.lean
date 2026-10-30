-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:51:16.798152+00:00
-- url     : https://prove2.me/theorems/b945c3b5-e581-4f1f-834e-ae5b3efa7949
-- title:
--   Edge lower bound for an inclusion-maximal planar drawing
-- statement:
--   A finite inclusion-maximal planar simple graph with at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
