-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_vertices__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
-- name    : WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:40.498888+00:00
-- url     : https://prove2.me/theorems/c8d20c40-a498-43d8-b4ed-abd0723d73a4
-- title:
--   Join distinct components of a planar drawing
-- statement:
--   Given a planar drawing and vertices in distinct connected components, there is a planar drawing of a supergraph on the same vertices that includes an edge between those vertices. This isolates the geometric redrawing operation needed by the target; a proof must arrange the components and route the new edge through the complement while preserving the injective vertex placement and noncrossing arc conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Adj u v := by sorry
