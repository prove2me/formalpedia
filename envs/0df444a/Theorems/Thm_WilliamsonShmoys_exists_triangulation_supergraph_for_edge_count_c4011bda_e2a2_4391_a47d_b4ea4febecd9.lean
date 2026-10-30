-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulation_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.exists_triangulation_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:18:17.318796+00:00
-- url     : https://prove2.me/theorems/962b94d7-bf99-4177-9904-f3b578ab1bfc
-- title:
--   A planar graph extends to a planar supergraph attaining the planar edge bound
-- statement:
--   Any drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulation_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
