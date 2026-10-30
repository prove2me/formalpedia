-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_bound
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:06:47.311559+00:00
-- url     : https://prove2.me/theorems/4494abcf-bf1f-4c70-8533-20caaf7ac1da
-- title:
--   Planar supergraph with the planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least `3|V|−6` edges. This isolates the triangulation-completion step. A proof route is to extend the given plane embedding to a maximal plane graph without adding vertices, then use Euler’s formula and the fact that every face of a maximal plane graph is triangular. This includes exactly three vertices, where completion is the triangle. The parent applies its maximality hypothesis to this extension and transfers the edge bound back by equality of edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Set.Subset P.edgeSet Q.edgeSet ∧
      3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by sorry
