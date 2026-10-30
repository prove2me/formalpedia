-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:24:26.357052+00:00
-- url     : https://prove2.me/theorems/77de69cb-c537-4581-bdbd-5f8e6aadfa5a
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This child isolates the planar topology and Euler-count argument: maximality makes the embedding triangular, after which Euler’s formula yields the count. The explicit size bound covers the three-vertex case and excludes smaller cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
