-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_292cccde_9238_49dd_bff4_dbc6d5d73c71_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_292cccde_9238_49dd_bff4_dbc6d5d73c71_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:13:19.81232+00:00
-- url     : https://prove2.me/theorems/fddb0f81-7944-4e99-898d-d807c45592e3
-- title:
--   Triangulated completion of a finite planar graph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_292cccde_9238_49dd_bff4_dbc6d5d73c71_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
