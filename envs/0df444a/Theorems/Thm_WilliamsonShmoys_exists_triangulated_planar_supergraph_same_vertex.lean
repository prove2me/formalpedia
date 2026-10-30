-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_same_vertex
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph_same_vertex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:39:48.975165+00:00
-- url     : https://prove2.me/theorems/a0d7916a-0378-4cc4-8609-751369741c85
-- title:
--   Triangulated supergraph on the same vertices
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges. The target’s maximality hypothesis then forces this extension to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph_same_vertex
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
