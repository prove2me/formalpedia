-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_completion_maximal_edge_count_37d910a7_7508_48a8_9dea_1ce0a7ac4e79
-- name    : WilliamsonShmoys.triangulation_completion_maximal_edge_count_37d910a7_7508_48a8_9dea_1ce0a7ac4e79
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:39:24.702285+00:00
-- url     : https://prove2.me/theorems/e3bc719b-bda8-4c11-b923-312be78eb315
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices that is maximal among drawable supergraphs has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_completion_maximal_edge_count_37d910a7_7508_48a8_9dea_1ce0a7ac4e79
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V, Q ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
