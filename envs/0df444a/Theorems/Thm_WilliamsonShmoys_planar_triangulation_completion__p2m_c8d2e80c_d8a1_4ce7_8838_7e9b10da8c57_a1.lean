-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:56.108136+00:00
-- url     : https://prove2.me/theorems/25e5c99b-0e98-467d-950b-52f83507dff1
-- title:
--   Triangulated planar completion with exact edge count
-- statement:
--   Every drawable finite simple graph on an ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
