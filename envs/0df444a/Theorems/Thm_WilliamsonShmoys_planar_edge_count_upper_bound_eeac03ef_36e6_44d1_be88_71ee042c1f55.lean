-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:14:19.948604+00:00
-- url     : https://prove2.me/theorems/ebd4cf02-7699-4f34-ae6d-7ed4775d8c5e
-- title:
--   Planar drawable graphs satisfy the Euler edge upper bound
-- statement:
--   A drawable simple graph on at least three vertices has at most 3n − 6 edges. Euler’s formula and face-edge incidence counting give the bound; disconnected components can be joined or handled componentwise.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
