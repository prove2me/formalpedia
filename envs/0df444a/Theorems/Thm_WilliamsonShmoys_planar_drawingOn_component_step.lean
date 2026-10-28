-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_component_step
-- name    : WilliamsonShmoys.planar_drawingOn_component_step
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:49:42.004399+00:00
-- url     : https://prove2.me/theorems/eff5c04a-7241-4689-905d-e9ab1995eb40
-- title:
--   Merge two components of a planar drawing
-- statement:
--   For a disconnected graph with the given finite drawing and at least three vertices, extend it to a planar-drawn supergraph that preserves every old reachable pair and makes at least one previously unreachable pair reachable. This is the local geometric augmentation step; adding a single arc between distinct components is a concrete proof route. The hypotheses exclude the empty vertex set, and the construction must respect the drawing predicate’s endpoint, injectivity, vertex-avoidance, and noncrossing requirements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_component_step
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V)
    (hnotConnected : ¬ P.Connected) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ u v, P.Reachable u v → Q.Reachable u v) ∧
      ∃ u v, ¬ P.Reachable u v ∧ Q.Reachable u v := by sorry
