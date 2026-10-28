-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_maximal_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:57:15.753714+00:00
-- url     : https://prove2.me/theorems/6c0819c8-795c-411a-aacd-f8cf4c691759
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A planar simple graph that is maximal among planar supergraphs on the same vertex set has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, HasPlanarDrawingOn U →
      (∀ u v, T.Adj u v → U.Adj u v) → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
