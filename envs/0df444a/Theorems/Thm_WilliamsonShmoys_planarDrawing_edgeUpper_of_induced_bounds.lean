-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper_of_induced_bounds
-- name    : WilliamsonShmoys.planarDrawing_edgeUpper_of_induced_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:12:36.841438+00:00
-- url     : https://prove2.me/theorems/6d693209-0f72-480b-9b64-c6bf5a75512d
-- title:
--   Aggregate connected induced-subgraph edge bounds
-- statement:
--   If every connected induced subgraph with at least three vertices satisfies the planar edge bound, then the whole graph satisfies it. This is purely combinatorial and does not assume planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_edgeUpper_of_induced_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (connectedInducedBound : ∀ (S : Finset V),
      (G.induce (↑S : Set V)).Connected →
      3 ≤ Fintype.card S →
      (G.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card S)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
