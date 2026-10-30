-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_completion__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:53.58305+00:00
-- url     : https://prove2.me/theorems/8549c90d-5e03-4132-87df-05240f9d6920
-- title:
--   Planar drawing completion to an edge-maximal supergraph
-- statement:
--   Every graph with a planar drawing has a planar supergraph on the same finite vertex type that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ J : SimpleGraph V, H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ (∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J) := by sorry
