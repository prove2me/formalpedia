-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:46.584962+00:00
-- url     : https://prove2.me/theorems/d8432cfb-4cfd-4c2a-9367-e9614f7d520c
-- title:
--   Restrict a plane drawing to a single-edge supergraph
-- statement:
--   If a drawn supergraph of K contains an edge between two vertices unreachable in K, then the drawing can be restricted to K plus that one edge, yielding the desired exact adjacency relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hKH : K ≤ H)
    (u v : V) (hUnreachable : ¬ K.Reachable u v) (hEdge : H.Adj u v) :
    ∃ H' : SimpleGraph V,
      HasPlanarDrawingOn H' ∧ K ≤ H' ∧
      ∀ x y : V,
        H'.Adj x y ↔
          K.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
