-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
-- name    : WilliamsonShmoys.planar_add_edge_between_unreachable__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:18.336112+00:00
-- url     : https://prove2.me/theorems/79f4dc92-0a20-4aaa-bbec-b4a4e2c2e492
-- title:
--   Adding an edge between unreachable vertices preserves planarity
-- statement:
--   For any finite ordered graph with a planar drawing, adding an edge between two vertices that are not connected by a path still yields a graph with a planar drawing. The drawing may be rebuilt, as the predicate asserts existence rather than preservation of a particular embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_unreachable__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (hSeparate : ¬ H.Reachable u v)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn (H ⊔ SimpleGraph.edge u v) := by
  sorry
