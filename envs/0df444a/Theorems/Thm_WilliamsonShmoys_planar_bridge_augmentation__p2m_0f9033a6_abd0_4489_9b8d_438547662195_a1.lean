-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_augmentation__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
-- name    : WilliamsonShmoys.planar_bridge_augmentation__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:30.340647+00:00
-- url     : https://prove2.me/theorems/9ff15d30-8739-4d4c-ada8-35f6650f3988
-- title:
--   Insert a planar bridge between disconnected components
-- statement:
--   A finite disconnected graph with a crossing-free drawing can be redrawn as a planar supergraph on the same vertices that contains at least one new edge. The new edge joins vertices in different components; the statement covers the smallest possible disconnected case, two isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

/-- Separate the components of a finite planar drawing and insert a bridge between two of them. -/

theorem WilliamsonShmoys.planar_bridge_augmentation__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K) (hnot : ¬ K.Connected) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∃ u v : V, L.Adj u v ∧ ¬ K.Adj u v := by sorry
