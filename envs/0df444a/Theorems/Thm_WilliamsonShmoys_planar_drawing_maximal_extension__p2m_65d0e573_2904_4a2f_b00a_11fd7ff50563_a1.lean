-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:24:10.292868+00:00
-- url     : https://prove2.me/theorems/ad631673-8271-47a3-82a5-74426b584d3d
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph on a fixed finite ordered vertex type is contained in a drawable supergraph maximal among drawable supergraphs on that same type. Maximality is stated explicitly against all drawable supergraphs, including equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V,
        Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by sorry
