-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_count_lower_bound_a564c908_f139_469a_b89f_75ea35d29efc
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_count_lower_bound_a564c908_f139_469a_b89f_75ea35d29efc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:19:13.028095+00:00
-- url     : https://prove2.me/theorems/308586e4-9210-49ca-8ad4-26b2ba28c74b
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices with no drawable proper supergraph on the same vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_count_lower_bound_a564c908_f139_469a_b89f_75ea35d29efc
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V, N <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M <= N) :
    3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by sorry
