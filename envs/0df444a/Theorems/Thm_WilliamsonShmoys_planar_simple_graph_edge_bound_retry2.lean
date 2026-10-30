-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_retry2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:46:18.810554+00:00
-- url     : https://prove2.me/theorems/68a21d27-29ba-4640-a9f9-b202f61345f5
-- title:
--   Euler edge bound for a drawable simple graph
-- statement:
--   A simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
