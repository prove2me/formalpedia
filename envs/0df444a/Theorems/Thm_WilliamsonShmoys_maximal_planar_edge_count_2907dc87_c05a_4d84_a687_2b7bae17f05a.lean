-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- name    : WilliamsonShmoys.maximal_planar_edge_count_2907dc87_c05a_4d84_a687_2b7bae17f05a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:10:39.473236+00:00
-- url     : https://prove2.me/theorems/a4893b45-3b05-4d2c-87ef-c1659380dc83
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A drawable simple graph on at least three finite vertices with no drawable proper supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_2907dc87_c05a_4d84_a687_2b7bae17f05a
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
