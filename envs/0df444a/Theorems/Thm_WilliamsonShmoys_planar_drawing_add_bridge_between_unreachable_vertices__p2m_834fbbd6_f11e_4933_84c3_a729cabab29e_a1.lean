-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_between_unreachable_vertices__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_between_unreachable_vertices__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:12:41.181278+00:00
-- url     : https://prove2.me/theorems/6b761602-ec4e-4b71-82d8-bcea18a590f0
-- title:
--   Add a bridge between unreachable vertices in a planar drawing
-- statement:
--   Given a planar drawing and two unreachable vertices, adding the edge between them preserves the existence of a planar drawing on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_bridge_between_unreachable_vertices__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (u v : V)
    (hnot : ¬ H.Reachable u v) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by sorry
