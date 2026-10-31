-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:16:26.70645+00:00
-- url     : https://prove2.me/theorems/3d35c422-26b2-44b6-842a-87c2ee457863
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
