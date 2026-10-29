-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:00:13.582842+00:00
-- url     : https://prove2.me/theorems/a564c908-f139-469a-b89f-75ea35d29efc
-- title:
--   Drawable planar supergraph edge lower bound
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has a drawable supergraph on the same vertices with at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph V, G <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by sorry
