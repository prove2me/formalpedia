-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_23341804_e9bd_4849_9be7_9e709bd142a9
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_23341804_e9bd_4849_9be7_9e709bd142a9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:44:41.584866+00:00
-- url     : https://prove2.me/theorems/371d51e0-7bc0-4b86-b239-3fe10e1c76f9
-- title:
--   Maximality forces the planar lower edge bound
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_23341804_e9bd_4849_9be7_9e709bd142a9
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
