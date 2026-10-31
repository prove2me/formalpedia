-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_b69f5d0b_8d80_4770_82d5_e0533af83150_a1
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_b69f5d0b_8d80_4770_82d5_e0533af83150_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:03.821971+00:00
-- url     : https://prove2.me/theorems/9ee840fe-9294-4975-9f98-00126b2211c0
-- title:
--   Every drawable graph extends to a triangulation
-- statement:
--   Any drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_b69f5d0b_8d80_4770_82d5_e0533af83150_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : ∃ J : SimpleGraph V, H <= J ∧ HasPlanarDrawingOn J ∧ J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
