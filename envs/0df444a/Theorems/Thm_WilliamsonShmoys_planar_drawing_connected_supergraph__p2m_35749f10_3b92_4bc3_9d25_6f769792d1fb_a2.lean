-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T07:15:34.947983+00:00
-- url     : https://prove2.me/theorems/4f0ec649-9547-4008-8805-0306b746033f
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing, retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ H : SimpleGraph V, (∀ e, e ∈ M.edgeSet → e ∈ H.edgeSet) ∧ (∀ u v, Relation.ReflTransGen H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
