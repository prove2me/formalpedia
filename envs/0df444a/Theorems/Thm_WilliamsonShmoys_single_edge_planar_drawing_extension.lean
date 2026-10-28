-- Prove2me | Theorems.Thm_WilliamsonShmoys_single_edge_planar_drawing_extension
-- name    : WilliamsonShmoys.single_edge_planar_drawing_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:14:10.411379+00:00
-- url     : https://prove2.me/theorems/9d37d8c6-716c-49ee-8c01-aa1e1ffeec68
-- title:
--   Join two components by one planar edge
-- statement:
--   For a disconnected drawable graph on at least three vertices, add exactly one edge between vertices in distinct components, preserving the drawing property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.single_edge_planar_drawing_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    Exists fun H : SimpleGraph V =>
      (Exists fun u : V => Exists fun v : V =>
        u ≠ v ∧ ¬ G.Reachable u v ∧
        (forall x y : V,
          H.Adj x y ↔ G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
