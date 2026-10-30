-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_strict_extension__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a4
-- name    : WilliamsonShmoys.planar_drawing_disconnected_strict_extension__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:09.977058+00:00
-- url     : https://prove2.me/theorems/22026dce-cf08-4d81-a1bc-1821774a6f8a
-- title:
--   Strict planar extension of a disconnected drawing
-- statement:
--   Every disconnected planar drawing on a finite linearly ordered vertex type with at least three vertices has a planar supergraph on the same vertex set with strictly more edges. The size hypothesis excludes the empty-vertex boundary case, where strict extension is impossible. This isolates the geometric extension required by the target; its remaining core is to construct the new crossing-free drawing after joining two components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_disconnected_strict_extension__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hdisc : ¬ K.Connected) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ K.edgeSet.ncard < H.edgeSet.ncard := by sorry
