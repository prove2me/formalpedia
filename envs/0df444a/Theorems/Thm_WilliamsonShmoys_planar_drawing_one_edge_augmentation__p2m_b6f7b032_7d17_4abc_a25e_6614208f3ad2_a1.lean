-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_augmentation__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
-- name    : WilliamsonShmoys.planar_drawing_one_edge_augmentation__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:11.087165+00:00
-- url     : https://prove2.me/theorems/68fcfb6b-9fe7-4d9c-85f0-a7b7f89a4ef9
-- title:
--   Add an edge between distinct components of a planar drawing
-- statement:
--   Every disconnected finite graph with a crossing-free drawing has two vertices in distinct components whose edge can be added while preserving a crossing-free drawing. The new graph has exactly the old edges plus that one undirected edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_one_edge_augmentation__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hnc : ¬ K.Connected) :
    ∃ a b : V, ∃ H : SimpleGraph V,
      ¬ K.Adj a b ∧ ¬ K.Reachable a b ∧
      (∀ u v, H.Adj u v ↔
        K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
