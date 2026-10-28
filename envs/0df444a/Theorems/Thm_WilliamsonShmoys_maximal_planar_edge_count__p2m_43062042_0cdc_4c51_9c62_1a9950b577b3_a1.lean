-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:16:26.698062+00:00
-- url     : https://prove2.me/theorems/a57dc3db-20ea-40d3-9b0f-dcd4c88e6cc2
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3n − 6 edges, expressed without subtraction as m + 6 = 3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
