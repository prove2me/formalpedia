-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:51:31.431244+00:00
-- url     : https://prove2.me/theorems/1652e93a-7659-436b-9a78-8097778e209b
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any finite graph with the supplied crossing-free drawing and at least three vertices can be extended, without changing its vertex type, to a connected graph with a crossing-free drawing, while retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_connected_planar_supergraph__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, (∀ u v, G.Adj u v → H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
