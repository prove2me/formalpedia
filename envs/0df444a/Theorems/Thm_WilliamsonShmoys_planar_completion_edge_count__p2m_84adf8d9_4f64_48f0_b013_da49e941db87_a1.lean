-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_84adf8d9_4f64_48f0_b013_da49e941db87_a1
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_84adf8d9_4f64_48f0_b013_da49e941db87_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:34:14.948405+00:00
-- url     : https://prove2.me/theorems/21bb1f42-93f8-4aca-8bd1-86213d966802
-- title:
--   Completion of a planar graph to a triangulation
-- statement:
--   Every finite drawable simple graph on at least three vertices is a subgraph of a drawable triangulation on the same vertex set, whose edge count is exactly 3|V|−6. This supplies the missing completion step; the parent’s maximality hypothesis identifies the completion with K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_84adf8d9_4f64_48f0_b013_da49e941db87_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
