-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
-- name    : WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:30.24733+00:00
-- url     : https://prove2.me/theorems/99b05842-3697-4e81-a13b-ad38ebc3f816
-- title:
--   Planar extension across distinct components
-- statement:
--   For a graph with a crossing-free drawing, if two vertices lie in different connected components, there is a strictly larger graph on the same vertices that adds an edge between them and still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hUV : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
