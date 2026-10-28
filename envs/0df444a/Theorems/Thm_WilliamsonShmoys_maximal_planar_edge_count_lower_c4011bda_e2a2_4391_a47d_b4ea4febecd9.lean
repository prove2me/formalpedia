-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:19:28.36153+00:00
-- url     : https://prove2.me/theorems/32cc2ad5-1015-458a-be0e-7806cb360ed5
-- title:
--   A maximal planar graph reaches the planar edge bound
-- statement:
--   A drawable graph on at least three vertices with no drawable proper supergraph on the same vertex set has at least 3n − 6 edges. Extend its drawing to a triangulation on the same vertices; maximality identifies the extension with the original graph, and Euler’s formula gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
