-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_20261026
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:25:26.358881+00:00
-- url     : https://prove2.me/theorems/c9b7b7e2-1041-44ba-9c5e-f8ae3acb39e1
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   This child removes the planar edge-count argument from the parent and preserves its necessary lower bound of three vertices. For a finite simple graph with the supplied crossing-free drawing, maximality implies the drawing is connected and every face is triangular: otherwise components can be joined, or an edge can be added across a face without a crossing. Euler’s formula and counting each edge on the boundaries of two faces then give |E| = 3|V| − 6, equivalent to the stated natural-number equality. The case of exactly three vertices is included and yields three edges. Formalizing the connectivity, face structure, and Euler count for the continuous-arc predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
