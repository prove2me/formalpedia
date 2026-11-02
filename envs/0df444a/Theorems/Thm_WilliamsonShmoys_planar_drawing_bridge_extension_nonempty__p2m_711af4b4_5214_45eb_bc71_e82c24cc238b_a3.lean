-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension_nonempty__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a3
-- name    : WilliamsonShmoys.planar_drawing_bridge_extension_nonempty__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:27:29.178591+00:00
-- url     : https://prove2.me/theorems/c404492e-8c81-4cec-a5ba-6ddb6067f960
-- title:
--   Add a planar edge between distinct components on a nonempty vertex type
-- statement:
--   For a finite linearly ordered vertex type with at least three elements, a disconnected graph with a planar drawing can be extended by adding exactly one edge between unreachable vertices while retaining a planar drawing. The proof constructs the new edge as an arc through the complement of the existing drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_bridge_extension_nonempty__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 <= Fintype.card V)
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v ∧
      ∃ P : SimpleGraph V,
        (∀ x y : V, P.Adj x y ↔
          G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
        WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
