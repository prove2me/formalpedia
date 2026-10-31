-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:46.295242+00:00
-- url     : https://prove2.me/theorems/b69f5d0b-8d80-4770-82d5-e0533af83150
-- title:
--   Lower bound for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three finite vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges. Establish that maximality forces a triangulation, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) (hmax : ∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) : 3 * Fintype.card V - 6 <= H.edgeSet.ncard := by sorry
