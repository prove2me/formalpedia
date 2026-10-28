-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_card
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_card
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:20:17.973997+00:00
-- url     : https://prove2.me/theorems/b74a49f4-b6ce-4a24-b33f-5907e2820ae4
-- title:
--   Planar supergraph with maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three is a subgraph of a planar graph on the same vertices with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_card {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hCard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
