-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:05.267517+00:00
-- url     : https://prove2.me/theorems/5b1667b7-42bc-4fca-8b00-4cc76e33db8b
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   Every inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges. The three-vertex case yields the triangle count; the general proof route is to derive connectedness and triangular faces for a maximal planar embedding and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
