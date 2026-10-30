-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_c76468fe
-- name    : WilliamsonShmoys.planar_edge_upper_bound_c76468fe
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:41:20.990893+00:00
-- url     : https://prove2.me/theorems/4eaca9a1-0b75-4064-af61-749b7b7175ea
-- title:
--   Euler upper bound for a planar graph
-- statement:
--   A graph with the given planar drawing on at least three vertices has at most 3n − 6 edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_c76468fe {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
