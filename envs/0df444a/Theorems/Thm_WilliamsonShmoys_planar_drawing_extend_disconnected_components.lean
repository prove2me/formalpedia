-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_disconnected_components
-- name    : WilliamsonShmoys.planar_drawing_extend_disconnected_components
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T01:42:20.26789+00:00
-- url     : https://prove2.me/theorems/b5e4f4a4-eed5-425a-aa91-3cc927b67a05
-- title:
--   Extend a disconnected planar graph by joining components
-- statement:
--   Any disconnected finite planar graph has a planar supergraph on the same vertices that adds at least one edge between old components, with every added edge joining old components. This gives the finite-completion theorem its required component-merging step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extend_disconnected_components
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hGdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) := by sorry
