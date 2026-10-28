-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair
-- name    : WilliamsonShmoys.maximal_planar_edge_count_repair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:37:05.39418+00:00
-- url     : https://prove2.me/theorems/1a9e3423-67b8-4196-8909-cc8d9eac42a0
-- title:
--   An inclusion-maximal drawable graph has the planar edge lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
