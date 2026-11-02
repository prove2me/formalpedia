-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_geometry__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_geometry__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:22.318852+00:00
-- url     : https://prove2.me/theorems/40d76f6e-d9c4-42d2-ac24-f14ba1b0b61d
-- title:
--   Extend a planar drawing by a bridge between components
-- statement:
--   Given a planar drawing and two nonadjacent vertices in different components, add exactly their undirected edge and produce a planar drawing of the resulting graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_bridge_geometry__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (a b : V)
    (hab : ¬ K.Adj a b)
    (hnotReachable : ¬ K.Reachable a b) :
    ∃ H : SimpleGraph V,
      (∀ u v, H.Adj u v ↔
        K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
