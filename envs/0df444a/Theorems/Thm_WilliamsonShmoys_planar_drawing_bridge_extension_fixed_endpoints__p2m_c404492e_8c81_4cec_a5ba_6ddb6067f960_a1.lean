-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension_fixed_endpoints__p2m_c404492e_8c81_4cec_a5ba_6ddb6067f960_a1
-- name    : WilliamsonShmoys.planar_drawing_bridge_extension_fixed_endpoints__p2m_c404492e_8c81_4cec_a5ba_6ddb6067f960_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:34.973095+00:00
-- url     : https://prove2.me/theorems/3bbfcf99-0ca1-4812-915c-8a51d6332e64
-- title:
--   Extend a planar drawing by joining fixed unreachable vertices
-- statement:
--   For any two unreachable vertices in a graph with a planar drawing, adding exactly the edge between them preserves the existence of a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_bridge_extension_fixed_endpoints__p2m_c404492e_8c81_4cec_a5ba_6ddb6067f960_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hnot : ¬ G.Reachable u v) :
    ∃ P : SimpleGraph V,
      (∀ x y : V, P.Adj x y ↔
        G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
