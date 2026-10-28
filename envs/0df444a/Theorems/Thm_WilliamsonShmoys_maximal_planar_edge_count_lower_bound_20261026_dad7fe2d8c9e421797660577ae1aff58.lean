-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:29:42.280274+00:00
-- url     : https://prove2.me/theorems/2e855238-1633-4b12-9ca3-4cc971538317
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal graph satisfying `HasPlanarDrawingOn` on at least three vertices has at least `3|V| − 6` edges, expressed as `3|V| ≤ edgeCount + 6`. A proof route is to extend its drawing, without adding vertices, until all faces are triangular; maximality forces the original graph already to have the triangulation's edge count. This child captures the extension and Euler-count obligation while retaining all parent hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall K' : SimpleGraph V, K <= K' ->
      WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
