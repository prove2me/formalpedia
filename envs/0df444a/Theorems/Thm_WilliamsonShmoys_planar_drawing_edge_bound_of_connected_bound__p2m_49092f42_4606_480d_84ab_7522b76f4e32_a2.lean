-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:21:38.053521+00:00
-- url     : https://prove2.me/theorems/7cfe8adb-3896-4a89-9953-f0bd38318921
-- title:
--   Extend the connected bound to disconnected drawings
-- statement:
--   If the stated edge bound holds for every connected graph with a crossing-free drawing and at least three vertices, it holds for any finite graph with such a drawing and at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2 (hconn : ∀ (W : Type) [Fintype W] [LinearOrder W] (Y : SimpleGraph W), Y.Connected → WilliamsonShmoys.HasPlanarDrawingOn Y → 3 ≤ Fintype.card W → Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card W) {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
