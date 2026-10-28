-- Prove2me | Theorems.Thm_WilliamsonShmoys_locally_maximal_planar_edge_bound__p2m_36354cce_e9f2_4cf3_abf4_0b18020ca45b_a1
-- name    : WilliamsonShmoys.locally_maximal_planar_edge_bound__p2m_36354cce_e9f2_4cf3_abf4_0b18020ca45b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:50:22.657154+00:00
-- url     : https://prove2.me/theorems/637d5aff-c0b4-44ca-8441-714e49c98d9c
-- title:
--   Edge bound for locally maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that admits no drawable supergraph with exactly one more edge has at least 3|V|−6 edges. This isolates the planar embedding and Euler-counting work needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.locally_maximal_planar_edge_bound__p2m_36354cce_e9f2_4cf3_abf4_0b18020ca45b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hNoOneEdgeExtension : ∀ L : SimpleGraph V, K ≤ L →
      L.edgeSet.ncard = K.edgeSet.ncard + 1 →
      WilliamsonShmoys.HasPlanarDrawingOn L → False) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
