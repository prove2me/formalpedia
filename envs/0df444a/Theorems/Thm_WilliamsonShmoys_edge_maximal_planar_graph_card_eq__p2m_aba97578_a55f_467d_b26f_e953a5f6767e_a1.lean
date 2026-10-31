-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:32.407904+00:00
-- url     : https://prove2.me/theorems/b387e51f-12e6-457e-b8c7-5aeeed4116ef
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that has a crossing-free drawing and admits no proper planar supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
