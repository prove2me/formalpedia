-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:43:21.848745+00:00
-- url     : https://prove2.me/theorems/e84be062-a88b-400f-ae1e-220de86dfe5f
-- title:
--   Euler upper bound for drawable graphs in the augmentation edge-count proof
-- statement:
--   Every finite drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
