-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_extension
-- name    : WilliamsonShmoys.planar_edge_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:59:13.237335+00:00
-- url     : https://prove2.me/theorems/661bd63e-8977-41b2-ad5e-663a3d9c3727
-- title:
--   A planar drawing extends across two components
-- statement:
--   For a drawable graph and an unreachable pair, construct a drawable strict supergraph whose only new adjacency is the edge joining that pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_extension
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) {u v : V}
    (huv : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H ∧
      ∀ a b, K.Adj a b ↔
        H.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by sorry
