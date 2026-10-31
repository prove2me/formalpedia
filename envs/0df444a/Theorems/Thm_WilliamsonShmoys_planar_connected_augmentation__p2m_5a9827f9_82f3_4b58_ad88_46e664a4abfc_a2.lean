-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
-- name    : WilliamsonShmoys.planar_connected_augmentation__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:53.492856+00:00
-- url     : https://prove2.me/theorems/471d3091-c665-452b-ba76-4b526ca802b5
-- title:
--   Connect components of a finite planar drawing by added edges
-- statement:
--   Any finite graph with a crossing-free drawing on its ordered vertex set has a connected simple supergraph on the same vertices with a crossing-free drawing. Its edge count is at least the original graph’s edge count. The claim also covers already connected graphs and graphs with isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_augmentation__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        M.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
