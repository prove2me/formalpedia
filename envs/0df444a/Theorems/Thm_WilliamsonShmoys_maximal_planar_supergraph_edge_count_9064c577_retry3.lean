-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_9064c577_retry3
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:19:42.314025+00:00
-- url     : https://prove2.me/theorems/a1f6ec2e-91b4-4b59-88a3-db46c5ea46df
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3n − 6 edges. This removes the triangulation and Euler-count argument from the parent, which only needs to choose a maximal drawable supergraph. A proof route is to show maximality forces every face to be triangular, apply Euler’s formula, and solve the resulting equations. At n = 3 the conclusion gives 3 edges; the cardinality bound is needed for the usual maximal-planar conclusion. Formalizing the connection between the packaged drawing predicate and face structure is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
