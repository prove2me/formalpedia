-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_survives_component_bridge__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
-- name    : WilliamsonShmoys.planar_drawing_survives_component_bridge__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:42.986376+00:00
-- url     : https://prove2.me/theorems/d262dc00-1efa-4b7e-beb6-2cda02069a0d
-- title:
--   Add an edge between distinct components of a planar drawing
-- statement:
--   A finite planar graph remains planar after adding an edge between two unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_survives_component_bridge__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (x y : V)
    (hxy : ¬ G.Reachable x y) :
    ∃ H : SimpleGraph V,
      (∀ u v, H.Adj u v ↔
        G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∧
      HasPlanarDrawingOn H := by sorry
