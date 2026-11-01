-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_maximal__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
-- name    : WilliamsonShmoys.planar_augmentation_edge_maximal__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:00.879262+00:00
-- url     : https://prove2.me/theorems/6afb7beb-d83c-4a0e-85aa-a97cbc1a9986
-- title:
--   Extend a planar drawing to an edge maximal supergraph
-- statement:
--   Every finite graph with a supplied crossing-free drawing has an edge maximal planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_edge_maximal__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
