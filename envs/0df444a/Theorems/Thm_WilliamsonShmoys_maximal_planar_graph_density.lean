-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_density
-- name    : WilliamsonShmoys.maximal_planar_graph_density
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:04:46.751132+00:00
-- url     : https://prove2.me/theorems/04eefd50-1f7a-4747-948a-5b892b077f97
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A planar simple graph on at least three vertices that has no strictly larger planar supergraph on the same vertex set has at least 3n−6 edges. The condition includes isolated and disconnected cases: maximality rules those out by allowing further planar edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_density
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
