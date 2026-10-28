-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_one_edge
-- name    : WilliamsonShmoys.planar_drawing_add_one_edge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:25:46.482559+00:00
-- url     : https://prove2.me/theorems/6e610b29-3993-448d-9f83-b72950e30fb5
-- title:
--   Extend a planar drawing between two components
-- statement:
--   Given a planar drawing and two vertices in different connected components, add an edge joining different old components while preserving planarity and ensuring every new edge joins different old components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_one_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ a b, H.Adj a b → G.Adj a b ∨ ¬ G.Reachable a b) ∧
      (∃ a b, H.Adj a b ∧ ¬ G.Reachable a b) := by sorry
