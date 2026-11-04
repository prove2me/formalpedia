-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_card__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
-- name    : WilliamsonShmoys.maximalPlanar_edge_card__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:22.207117+00:00
-- url     : https://prove2.me/theorems/0824c1d6-466a-4e4b-9fa4-6bf9ba62d2e9
-- title:
--   Exact edge count for a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V| - 6 edges. Maximality forces every face in a planar embedding to be triangular; Euler's formula and counting face-edge incidences then give the equality, including the three-vertex triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanar_edge_card__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ K' : SimpleGraph V, K ≤ K' → HasPlanarDrawingOn K' → K' = K)
    (hn : 3 ≤ Fintype.card V) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
