-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_subgraph
-- name    : WilliamsonShmoys.edge_count_mono_of_subgraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:04:36.380276+00:00
-- url     : https://prove2.me/theorems/e0ccc7b7-6c3b-4553-9405-c536762841cc
-- title:
--   Monotonicity of edge count under subgraph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, subgraph inclusion implies that the edge count cannot decrease.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_of_subgraph {V : Type} [Fintype V] [LinearOrder V] (H K : SimpleGraph V) (hHK : H ≤ K) : H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
