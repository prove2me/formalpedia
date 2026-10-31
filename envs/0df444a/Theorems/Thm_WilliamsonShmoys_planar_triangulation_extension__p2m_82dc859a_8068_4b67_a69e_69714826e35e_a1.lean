-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_82dc859a_8068_4b67_a69e_69714826e35e_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_82dc859a_8068_4b67_a69e_69714826e35e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:11.433206+00:00
-- url     : https://prove2.me/theorems/5db12fa6-6ddb-45ce-9ff4-a1f528d0a813
-- title:
--   Maximal planar extension on the same vertices
-- statement:
--   Any finite simple connected graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_82dc859a_8068_4b67_a69e_69714826e35e_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hconn : H.Connected) (hV : 3 <= Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
