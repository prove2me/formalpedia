-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count_719d44f8
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count_719d44f8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:08:44.229914+00:00
-- url     : https://prove2.me/theorems/3e869d1e-d221-44f3-8f2b-71d5fc6eb8db
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraph inclusion has exactly 3|V|−6 edges. The proof route is to use maximality to show the drawing yields a connected triangulation: any missing edge that can be added inside a nontriangular face contradicts maximality. Then Euler’s formula and counting each face-edge incidence twice give the equality. The assumption |V| ≥ 3 is needed for this triangulation argument and the face count; the equality handles |V| = 3 with three edges. This is the remaining mathematical core; a formal proof must connect the stated arc-based drawing predicate to the planar embedding and face-count results.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count_719d44f8
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
