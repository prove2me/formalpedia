-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_bridge_across_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
-- name    : WilliamsonShmoys.planar_add_bridge_across_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:15.645583+00:00
-- url     : https://prove2.me/theorems/05c1a0b4-69ca-4d36-9f49-0774601d7f45
-- title:
--   Add a planar bridge across an edge-free cut
-- statement:
--   A planar graph with an edge-free cut separating `u` and `v` has a planar supergraph on the same vertices that includes the edge `u-v`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_bridge_across_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (A : Set V) (huA : u ∈ A) (hvA : v ∉ A)
    (hcut : ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ G.Adj x y) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
