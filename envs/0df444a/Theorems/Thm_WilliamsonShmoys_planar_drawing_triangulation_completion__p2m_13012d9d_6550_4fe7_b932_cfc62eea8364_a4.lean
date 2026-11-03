-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_13012d9d_6550_4fe7_b932_cfc62eea8364_a4
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_13012d9d_6550_4fe7_b932_cfc62eea8364_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:44.212722+00:00
-- url     : https://prove2.me/theorems/f1bb4dd5-e49f-44e4-9180-96043403f197
-- title:
--   Completion of a planar drawing to a maximal edge-count graph
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable simple graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_13012d9d_6550_4fe7_b932_cfc62eea8364_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
