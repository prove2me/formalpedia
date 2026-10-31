-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:27.089145+00:00
-- url     : https://prove2.me/theorems/98819be2-b7a0-4e40-9594-ea97bee4d16d
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every graph with a crossing-free drawing has a planar supergraph on the same finite ordered vertex type that is maximal among planar supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hPlanar : HasPlanarDrawingOn J) : ∃ H : SimpleGraph V, HasPlanarDrawingOn H ∧ J.edgeSet.ncard ≤ H.edgeSet.ncard ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
