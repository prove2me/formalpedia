-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:42.153797+00:00
-- url     : https://prove2.me/theorems/41f5a52f-01af-4de8-a0be-72b7b0223cd9
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   A drawable simple graph on at least three finite vertices has at most 3|V|−6 edges. Prove by Euler counting, handling disconnected graphs componentwise.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
