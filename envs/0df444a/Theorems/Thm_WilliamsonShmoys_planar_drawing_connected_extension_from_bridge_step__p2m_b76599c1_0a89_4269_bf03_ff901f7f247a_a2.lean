-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_from_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:06.789981+00:00
-- url     : https://prove2.me/theorems/3750f754-8764-46ea-8741-399ac1e39bbe
-- title:
--   Use a bridge step and finite maximality to connect the drawing
-- statement:
--   Given the bridge step for every disconnected planar graph on a fixed nonempty finite ordered vertex type, any planar graph on that type has a connected planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 0 < Fintype.card V)
    (bridgeStep : ∀ (G : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G →
      (¬ ∀ u v, Relation.ReflTransGen G.Adj u v) →
      ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∃ u v, ¬ Relation.ReflTransGen G.Adj u v ∧ H.Adj u v)
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
