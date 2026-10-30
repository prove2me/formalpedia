-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_9064c577_retry2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:18:38.541208+00:00
-- url     : https://prove2.me/theorems/b9ff4b16-3c90-4e6c-a882-ea00a5db2636
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3n − 6 edges. The proof route formalizes the triangular-face property of maximal drawings and combines it with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
