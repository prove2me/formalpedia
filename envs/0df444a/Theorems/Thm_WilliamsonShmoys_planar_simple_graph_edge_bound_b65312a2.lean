-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_b65312a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_b65312a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T04:56:49.890851+00:00
-- url     : https://prove2.me/theorems/5d85cad7-27de-4b5f-ba62-c4df5e390bd5
-- title:
--   Edge bound for every finite simple planar graph
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing as encoded by HasPlanarDrawingOn has at most 3n−6 edges. This stronger planar density theorem implies the target without using maximality. A proof can extend the drawing to a maximal planar supergraph, obtain the plane embedding, and use Euler’s formula and face-edge incidence counting; the formalization must connect the custom continuous-arc drawing definition to that combinatorial embedding argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_b65312a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
