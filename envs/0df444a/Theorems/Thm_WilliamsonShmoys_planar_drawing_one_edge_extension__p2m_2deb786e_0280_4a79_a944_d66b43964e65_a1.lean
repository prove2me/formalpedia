-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_extension__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
-- name    : WilliamsonShmoys.planar_drawing_one_edge_extension__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:36.473657+00:00
-- url     : https://prove2.me/theorems/436e99a4-4132-415e-a9e0-141abe1502a3
-- title:
--   Extend a disconnected planar drawing by one edge
-- statement:
--   For a finite disconnected graph with a drawing satisfying the target's exact predicates, add an edge between previously disconnected vertices and obtain another graph on the same vertices with a valid drawing. The new edge connects different components, so it was not already present. This is the geometric extension step: choose an arc through the unbounded face joining the components, taking care that isolated vertices are included. A proof route is to use the finite embedded arcs and vertex set to choose a crossing-free route through that face, then parameterize the route as a continuous injective arc and verify its endpoint, vertex-avoidance, and edge-intersection conditions. The main remaining obligation is this topological construction in Lean, including its degeneracies for isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_one_edge_extension__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hGnc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      (∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) ∧
      HasPlanarDrawingOn H := by sorry
