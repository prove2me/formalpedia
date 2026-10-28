-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_disconnected_components_v3
-- name    : WilliamsonShmoys.planar_drawing_extend_disconnected_components_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:06:30.634407+00:00
-- url     : https://prove2.me/theorems/f832ed3f-096e-43d7-bc91-68ff2f662e30
-- title:
--   Join components of a finite planar drawing
-- statement:
--   For a disconnected finite graph on at least three vertices with a planar drawing, extend it on the same vertices to a planar supergraph. Every new edge joins vertices from distinct original components, and at least one such edge is added.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extend_disconnected_components_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) (hGdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) := by sorry
