-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_connected_augmentation__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
-- name    : WilliamsonShmoys.planarDrawingOn_connected_augmentation__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:17:33.999314+00:00
-- url     : https://prove2.me/theorems/8f1ceaba-890d-4ee2-90c3-c45d4b9ef67f
-- title:
--   Connected planar supergraph of a finite drawing
-- statement:
--   Any finite graph with the given crossing-free drawing has a connected planar supergraph on the same vertices. This includes drawings with isolated vertices and disconnected components; adding edges preserves the original edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_connected_augmentation__p2m_7f5185ee_24ca_4414_b90e_b6691f6b37ff_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧ N.Connected ∧ HasPlanarDrawingOn N := by sorry
