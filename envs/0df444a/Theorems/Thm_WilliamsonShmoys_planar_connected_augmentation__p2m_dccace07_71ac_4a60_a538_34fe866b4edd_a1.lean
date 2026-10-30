-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- name    : WilliamsonShmoys.planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:55.126366+00:00
-- url     : https://prove2.me/theorems/e3c38815-b74a-4448-8999-9891a739182d
-- title:
--   Connected planar augmentation on the same vertices
-- statement:
--   A drawable finite simple graph with at least three vertices has a connected drawable supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
