-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_lower_bound_exact_arcs
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound_exact_arcs
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:10:15.613282+00:00
-- url     : https://prove2.me/theorems/534a7c2b-92cb-487c-be70-82df334072d1
-- title:
--   Maximal drawable graph reaches the planar edge bound for the exact drawing predicate
-- statement:
--   A graph drawable by the exact `HasPlanarDrawingOn` predicate, maximal among drawable supergraphs on the same vertex type, and having at least three vertices has at least 3|V|−6 edges. The proof route augments the embedding to a triangulation and applies maximality to rule out any added edge; the three-vertex case is the complete triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound_exact_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
