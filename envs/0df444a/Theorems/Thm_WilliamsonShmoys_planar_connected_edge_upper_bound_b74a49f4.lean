-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound_b74a49f4
-- name    : WilliamsonShmoys.planar_connected_edge_upper_bound_b74a49f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:41:26.025051+00:00
-- url     : https://prove2.me/theorems/07d10d27-8119-47ea-84a5-c8ea905e45f1
-- title:
--   Connected planar edge bound
-- statement:
--   A connected finite simple graph with a crossing-free drawing on at least three vertices has at most 3n − 6 edges. Prove this by deriving Euler’s formula and the face-degree bound from the drawing predicate, then combine them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_upper_bound_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hConnected : K.Connected) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
