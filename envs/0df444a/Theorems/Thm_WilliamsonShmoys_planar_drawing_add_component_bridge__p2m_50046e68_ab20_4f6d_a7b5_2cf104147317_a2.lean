-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_component_bridge__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
-- name    : WilliamsonShmoys.planar_drawing_add_component_bridge__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:17:30.466794+00:00
-- url     : https://prove2.me/theorems/9a24a15d-98f8-4d34-9568-87e24095ac5d
-- title:
--   Add a suitable planar bridge between components
-- statement:
--   For a finite graph with a crossing-free drawing that is disconnected, choose two vertices in different components and add the edge between a suitable pair while preserving a crossing-free drawing. The endpoints are existentially chosen; the lemma does not claim that arbitrary prescribed endpoints can be joined.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_component_bridge__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hGnot : ¬ G.Connected) :
    ∃ u v : V, ∃ H : SimpleGraph V,
      ¬ G.Adj u v ∧ G ≤ H ∧ H.Adj u v ∧ HasPlanarDrawingOn H := by sorry
