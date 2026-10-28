-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_disconnected_components_v2
-- name    : WilliamsonShmoys.planar_drawing_extend_disconnected_components_v2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T09:18:29.665015+00:00
-- url     : https://prove2.me/theorems/2b18eee0-0982-4d81-92b2-e5215e97c9d5
-- title:
--   Extend a disconnected planar drawing by joining components
-- statement:
--   For any disconnected finite graph with a planar drawing, extend it on the same vertices to a planar supergraph that adds at least one edge between old components and adds no edge within an old component. This is the component-joining step required by the proved finite-completion theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extend_disconnected_components_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hGdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) := by sorry
