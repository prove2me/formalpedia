-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_on_euler_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_on_euler_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:18:22.850869+00:00
-- url     : https://prove2.me/theorems/7bfae1f5-e1f2-4c36-8c6c-a1ff958f0cfc
-- title:
--   Maximal planar drawings satisfy the Euler edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_on_euler_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ W : SimpleGraph V, HasPlanarDrawingOn W →
      (∀ u v, U.Adj u v → W.Adj u v) → W = U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry
