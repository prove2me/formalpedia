-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarGraphCanBeExtended_belowTriangulationBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2
-- name    : WilliamsonShmoys.planarGraphCanBeExtended_belowTriangulationBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:13.069686+00:00
-- url     : https://prove2.me/theorems/8bebbcb3-63fa-47e0-bd08-43c40080b6a9
-- title:
--   Strict planar extension below the triangulation bound
-- statement:
--   A drawable graph on at least three vertices whose edge count is strictly below 3|V|−6 has a strictly larger drawable supergraph on the same vertices. This supplies the contradiction to maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarGraphCanBeExtended_belowTriangulationBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) (hlt : M.edgeSet.ncard + 6 < 3 * Fintype.card V) : ∃ N : SimpleGraph V, LE.le M N ∧ HasPlanarDrawingOn N ∧ N ≠ M := by sorry
