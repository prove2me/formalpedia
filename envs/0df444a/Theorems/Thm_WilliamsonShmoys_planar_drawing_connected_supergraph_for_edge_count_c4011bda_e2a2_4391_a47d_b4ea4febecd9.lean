-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:20:42.654383+00:00
-- url     : https://prove2.me/theorems/0eaeae48-ca39-4818-a504-bddb7c4b7de2
-- title:
--   Extend a planar drawing to a connected supergraph
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing. This separates the disconnected-components issue from the Euler count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
