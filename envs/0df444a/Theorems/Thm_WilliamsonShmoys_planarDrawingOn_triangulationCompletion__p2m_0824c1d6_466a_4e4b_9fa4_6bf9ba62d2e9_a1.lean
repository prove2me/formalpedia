-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulationCompletion__p2m_0824c1d6_466a_4e4b_9fa4_6bf9ba62d2e9_a1
-- name    : WilliamsonShmoys.planarDrawingOn_triangulationCompletion__p2m_0824c1d6_466a_4e4b_9fa4_6bf9ba62d2e9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:35.595141+00:00
-- url     : https://prove2.me/theorems/ff18b25b-a5e2-42d5-a9ba-9dc0688f14d5
-- title:
--   Triangulation completion of a finite drawable graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. The edge-count assertion is independent of the chosen decidable-adjacency instance.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_triangulationCompletion__p2m_0824c1d6_466a_4e4b_9fa4_6bf9ba62d2e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ K' : SimpleGraph V, K ≤ K' ∧ HasPlanarDrawingOn K' ∧
      (∀ [DecidableRel K'.Adj], K'.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
