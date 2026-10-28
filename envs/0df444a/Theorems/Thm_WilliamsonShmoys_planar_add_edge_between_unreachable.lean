-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable
-- name    : WilliamsonShmoys.planar_add_edge_between_unreachable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:47:37.312973+00:00
-- url     : https://prove2.me/theorems/8c519880-ed14-4bde-9d30-e2d16db44693
-- title:
--   Add a bridge between disconnected vertices in a planar drawing
-- statement:
--   For any two vertices in different connected components of a graph with a crossing-free drawing, there is a planar graph on the same vertex type whose edge set strictly contains the original edge set. This is a reusable bridge-extension result and carries the principal geometric work. A proof route is to restrict the finite drawing to components, re-embed the two marked components so each marked vertex has an accessible outer-face sector, and join them through those sectors with a new arc that avoids every existing vertex and edge; place the other finitely many components away from that arc. Add only the edge between u and v. Non-reachability guarantees that u and v are distinct and that this edge was absent, which establishes strict inclusion. The definition requires verifying continuity, injectivity, endpoint conditions, and the nonintersection condition for the new arc against every existing edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_unreachable
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (hUV : ¬ K.Reachable u v) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
