-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_between_components__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
-- name    : WilliamsonShmoys.planar_drawing_bridge_between_components__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:46.898715+00:00
-- url     : https://prove2.me/theorems/bb97e785-1890-4d14-88f3-dc79ef1d3e81
-- title:
--   Add a planar edge between specified disconnected vertices
-- statement:
--   Given a planar drawing of a finite graph and two vertices in different components, there is a planar supergraph on the same vertices containing the edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_bridge_between_components__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Adj u v := by sorry
