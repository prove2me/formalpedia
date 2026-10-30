-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_planar_drawing
-- name    : WilliamsonShmoys.planar_edge_bound_of_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:14:34.835531+00:00
-- url     : https://prove2.me/theorems/59c300bc-73d6-44ab-ad6f-e9d4a576450c
-- title:
--   Simple planar edge bound from a drawing
-- statement:
--   A finite simple graph with at least three vertices and the specified planar drawing has at most 3|V| − 6 edges, stated as |E| + 6 ≤ 3|V| to avoid truncated subtraction. The bound allows disconnected graphs and includes the exact three-vertex boundary. A proof can first extend the drawing to a maximal planar graph, apply the face-degree incidence bound and Euler’s formula there, then transfer the edge bound to the subgraph. This gives the parent’s inequality; the remaining obligation is the planar incidence and extension argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_of_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
