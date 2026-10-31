-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_supergraph__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- name    : WilliamsonShmoys.planar_drawing_has_connected_supergraph__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:35.555648+00:00
-- url     : https://prove2.me/theorems/7397eada-aa5d-4bc5-889b-e16ea7056544
-- title:
--   Connect components of a planar drawing by added edges
-- statement:
--   Every finite graph with a crossing-free drawing on the fixed vertex set has a connected supergraph on that same vertex set that also has a crossing-free drawing. The original edge count is at most the supergraph’s edge count. This isolates the geometric task of joining distinct drawing components without introducing crossings; it can be proved by adding arcs through the complement between components, one component at a time. The construction adds edges only, so the edge-count inequality follows from inclusion. This child does not assert the Euler bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_connected_supergraph__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧ H.edgeSet.ncard ≤ G.edgeSet.ncard := by sorry
