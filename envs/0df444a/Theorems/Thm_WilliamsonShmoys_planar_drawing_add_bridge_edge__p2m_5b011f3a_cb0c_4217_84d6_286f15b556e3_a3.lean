-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_edge__p2m_5b011f3a_cb0c_4217_84d6_286f15b556e3_a3
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_edge__p2m_5b011f3a_cb0c_4217_84d6_286f15b556e3_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:34.390299+00:00
-- url     : https://prove2.me/theorems/fc3edf5b-5720-4dac-80b3-372c812aa4a0
-- title:
--   Preserve a planar drawing when bridging disconnected vertices
-- statement:
--   Given a planar drawing of a finite graph and distinct vertices in separate components, construct a planar drawing of the graph with exactly one added undirected edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_bridge_edge__p2m_5b011f3a_cb0c_4217_84d6_286f15b556e3_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v) (hnotreach : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      (∀ a b, K.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
      HasPlanarDrawingOn K := by
  sorry
