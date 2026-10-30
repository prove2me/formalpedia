-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_component_edge_bound__p2m_5598e679_4b8f_483d_bd76_05b90ab9d984_a3
-- name    : WilliamsonShmoys.planar_connected_component_edge_bound__p2m_5598e679_4b8f_483d_bd76_05b90ab9d984_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:02:22.596543+00:00
-- url     : https://prove2.me/theorems/5a92b84a-3e46-4764-99ac-2a1962855947
-- title:
--   Restrict a planar drawing to each connected component
-- statement:
--   For each component with at least three vertices, restrict the drawing witnesses to the component, establish that its component graph is connected, and apply the assumed connected edge bound. The explicit local `Fintype c` addresses the missing instance from the previous attempt.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_component_edge_bound__p2m_5598e679_4b8f_483d_bd76_05b90ab9d984_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (K : SimpleGraph W),
        HasPlanarDrawingOn K → K.Connected →
        3 ≤ Fintype.card W →
        K.edgeSet.ncard + 6 ≤ 3 * Fintype.card W) :
    ∀ c : M.ConnectedComponent, ∀ [Fintype c],
      3 ≤ Fintype.card c →
      (c.toSimpleGraph).edgeSet.ncard + 6 ≤ 3 * Fintype.card c := by sorry
