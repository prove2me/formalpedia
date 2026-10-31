-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_if_sparse__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
-- name    : WilliamsonShmoys.planar_edge_augmentation_if_sparse__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:59.970741+00:00
-- url     : https://prove2.me/theorems/a5cf4edc-e88b-40ef-a197-b0d2fda5eb44
-- title:
--   A sparse drawable graph has a drawable strict supergraph
-- statement:
--   A finite drawable simple graph with at least three vertices and strictly fewer than three times its vertex count minus six edges has a drawable strict supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_if_sparse__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hSparse : K.edgeSet.ncard + 6 < 3 * Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ HasPlanarDrawingOn L := by sorry
