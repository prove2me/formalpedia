-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_completion_with_maximal_edge_count_0319396f
-- name    : WilliamsonShmoys.exists_planar_completion_with_maximal_edge_count_0319396f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:39:48.788284+00:00
-- url     : https://prove2.me/theorems/95e100fa-cb2a-47e1-8a71-51d44bd3f28a
-- title:
--   Completion of a drawable graph to a maximal planar graph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This is the topological completion step; the parent theorem follows by applying maximality to that supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_completion_with_maximal_edge_count_0319396f
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
