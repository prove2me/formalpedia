-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_connected
-- name    : WilliamsonShmoys.maximal_planar_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:52:09.229053+00:00
-- url     : https://prove2.me/theorems/9795f6dc-1437-4893-a74b-eba4c499b6f6
-- title:
--   Maximal planar graphs are connected
-- statement:
--   A finite graph with at least three vertices that has a crossing-free drawing and is maximal among drawable graphs on the same vertex type is connected. This isolates the maximality argument; a proof can join two components through the complement of their disjoint plane drawings and contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.Connected := by sorry
