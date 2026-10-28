-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound_af1db6be
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound_af1db6be
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:58:18.213254+00:00
-- url     : https://prove2.me/theorems/9117bd9c-df36-4680-bf40-0829e0b4242c
-- title:
--   Planar graphs satisfy the simple edge bound
-- statement:
--   A graph with the stated crossing-free drawing on at least three vertices has at most 3|V|−6 edges. This isolates the Euler edge-counting step; a proof can count faces in each connected component and combine the component bounds. The condition |V| ≥ 3 supplies the needed size bound, including disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound_af1db6be {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
