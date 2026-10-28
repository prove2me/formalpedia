-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_maximal_case_7121c0f2
-- name    : WilliamsonShmoys.simple_planar_edge_bound_maximal_case_7121c0f2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:09:42.769461+00:00
-- url     : https://prove2.me/theorems/0e35fcc0-eb5f-499f-a7de-e76107bb51b5
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at most three times its vertex count minus six edges. This isolates the embedding, maximality, and Euler-count argument from the finite completion step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_bound_maximal_case_7121c0f2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall H : SimpleGraph V, G <= H ->
      WilliamsonShmoys.HasPlanarDrawingOn H -> H <= G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
