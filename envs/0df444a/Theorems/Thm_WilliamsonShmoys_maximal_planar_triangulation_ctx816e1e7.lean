-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_ctx816e1e7
-- name    : WilliamsonShmoys.maximal_planar_triangulation_ctx816e1e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:20:48.661909+00:00
-- url     : https://prove2.me/theorems/ffb2aee4-beb8-4160-b1e5-f617627ff233
-- title:
--   Every finite planar drawing extends to a triangulation
-- statement:
--   Any drawable simple graph on a fixed finite vertex set of size at least three is a subgraph of a drawable triangulation on that same vertex set, whose edge count satisfies Euler’s triangulation formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_triangulation_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ Q : SimpleGraph V,
      W ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
