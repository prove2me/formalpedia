-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_6d943741_fae6_4c58_9301_d8625eecfd1e_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_6d943741_fae6_4c58_9301_d8625eecfd1e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:27.275283+00:00
-- url     : https://prove2.me/theorems/46586232-d6f1-45ab-8e52-c7b70d794aee
-- title:
--   A deficient planar graph admits a strict planar extension
-- statement:
--   If a finite graph on at least three vertices has a crossing-free drawing and fewer than 3|V|−6 edges, then it has a strict supergraph on the same vertex type that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_6d943741_fae6_4c58_9301_d8625eecfd1e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K < L ∧ HasPlanarDrawingOn L := by sorry
