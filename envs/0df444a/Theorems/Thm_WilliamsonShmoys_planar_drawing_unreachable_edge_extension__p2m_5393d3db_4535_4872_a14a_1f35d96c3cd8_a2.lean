-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_unreachable_edge_extension__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
-- name    : WilliamsonShmoys.planar_drawing_unreachable_edge_extension__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:08.741483+00:00
-- url     : https://prove2.me/theorems/7b51bdb4-4dea-43b6-9d51-b05a3b3a7c9a
-- title:
--   A planar drawing can be extended between unreachable vertices
-- statement:
--   If a drawable graph has two distinct unreachable vertices, it has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_unreachable_edge_extension__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (u v : V)
    (huv : u ≠ v)
    (hUnreachable : ¬ M.Reachable u v) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by
  sorry
