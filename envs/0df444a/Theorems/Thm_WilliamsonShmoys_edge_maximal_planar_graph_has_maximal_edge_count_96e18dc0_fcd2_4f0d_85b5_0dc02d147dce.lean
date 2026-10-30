-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_maximal_edge_count_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_maximal_edge_count_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:08:32.963337+00:00
-- url     : https://prove2.me/theorems/f551cd7a-0a92-444e-a625-972b0546c624
-- title:
--   An edge-maximal drawable graph has the maximal planar edge count
-- statement:
--   A finite edge-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges. The standard route proves connectedness and triangular faces from maximality, then applies Euler’s formula and counts face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_maximal_edge_count_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
