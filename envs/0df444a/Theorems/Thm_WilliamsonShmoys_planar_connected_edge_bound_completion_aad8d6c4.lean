-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound_completion_aad8d6c4
-- name    : WilliamsonShmoys.planar_connected_edge_bound_completion_aad8d6c4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:36:04.096989+00:00
-- url     : https://prove2.me/theorems/43124a08-e00c-4a1a-ad63-e868e93f9e49
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing has a planar supergraph on the same vertices, containing every original edge, whose edge count is exactly 3n−6; consequently its original edge count is no greater.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_bound_completion_aad8d6c4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K.edgeSet ⊆ H.edgeSet ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
