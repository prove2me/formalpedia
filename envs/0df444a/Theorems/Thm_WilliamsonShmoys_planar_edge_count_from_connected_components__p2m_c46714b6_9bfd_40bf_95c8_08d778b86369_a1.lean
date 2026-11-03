-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_from_connected_components__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
-- name    : WilliamsonShmoys.planar_edge_count_from_connected_components__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:46.161576+00:00
-- url     : https://prove2.me/theorems/bf74435a-e03f-4081-bb2c-21c925387e99
-- title:
--   Reduce the planar edge bound to connected components
-- statement:
--   Reduce the general drawing bound to its connected-graph version by partitioning the vertices into connected components and restricting the drawing to each component. Components of size one contribute no edges; components of size two contribute at most one. For components of size at least three use `hconn`. Sum the component edge counts, handling separately the case with no component of size at least three. This step preserves the original `n ≥ 3` condition, including disconnected graphs and isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_from_connected_components__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H)
    (hconn : ∀ (W : Type) [Fintype W] [LinearOrder W] (K : SimpleGraph W),
      3 ≤ Fintype.card W → K.Connected → HasPlanarDrawingOn K →
      K.edgeSet.ncard + 6 ≤ 3 * Fintype.card W) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
