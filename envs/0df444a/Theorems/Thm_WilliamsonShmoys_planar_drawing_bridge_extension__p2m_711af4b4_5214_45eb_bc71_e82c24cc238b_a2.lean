-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
-- name    : WilliamsonShmoys.planar_drawing_bridge_extension__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:13.343439+00:00
-- url     : https://prove2.me/theorems/40f2f200-73c9-4b9b-b813-2c791360a464
-- title:
--   Add a planar edge between distinct components
-- statement:
--   For any finite ordered vertex type and any disconnected graph with a planar drawing, there are vertices in distinct connected components such that adding exactly the edge between them yields another graph with a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_bridge_extension__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v ∧
      ∃ P : SimpleGraph V,
        (∀ x y : V, P.Adj x y ↔
          G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
        WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
