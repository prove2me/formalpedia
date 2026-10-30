-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
-- name    : WilliamsonShmoys.planar_drawing_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:09.02038+00:00
-- url     : https://prove2.me/theorems/399eeee6-4234-4eb0-9aa5-260fcba2f92a
-- title:
--   Add a planar bridge between disconnected drawing components
-- statement:
--   A disconnected graph on a nonempty finite ordered vertex type with a crossing-free drawing has a crossing-free supergraph on the same vertices with an edge joining two vertices that were in different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 0 < Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ ∀ u v, Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v, ¬ Relation.ReflTransGen G.Adj u v ∧ H.Adj u v := by sorry
