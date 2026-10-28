-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_edge_ncard
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_edge_ncard
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:09:37.268553+00:00
-- url     : https://prove2.me/theorems/43806dc5-6d07-43bd-8ff5-bb34f7ace9cd
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   A finite graph on at least three vertices with a crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing, adding edges as needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_edge_ncard {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
