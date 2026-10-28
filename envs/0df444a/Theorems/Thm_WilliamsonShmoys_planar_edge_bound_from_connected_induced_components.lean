-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced_components
-- name    : WilliamsonShmoys.planar_edge_bound_from_connected_induced_components
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:59:11.054416+00:00
-- url     : https://prove2.me/theorems/51d7e70c-c0cf-4a02-9175-696dc28676f9
-- title:
--   Combine edge bounds across connected components
-- statement:
--   If every finite connected induced subgraph with at least three vertices satisfies the planar edge bound, then the whole graph satisfies it. The reduction partitions into connected components, uses the bound for larger components, and handles components of size one or two directly; the whole-graph lower bound ensures the small-component cases still yield the claimed global inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_connected_induced_components
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ (W : Set V) [Fintype W],
      3 ≤ Fintype.card W →
      (K.induce W).Connected →
      (K.induce W).edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
