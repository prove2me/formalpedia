-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_ge3_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- name    : WilliamsonShmoys.planar_connected_supergraph_ge3_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:21:41.37285+00:00
-- url     : https://prove2.me/theorems/f630f804-3de0-4080-af2a-09c2c9e64cec
-- title:
--   Connect a planar drawing with at least three vertices
-- statement:
--   Extend the drawn graph to a connected graph on the same vertex type while preserving planarity, assuming the vertex type has at least three elements. A proof route is to connect components by arcs through the complement of the finite embedded graph, with the size hypothesis excluding small-set boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_ge3_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
