-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_dd73cac9_b90d_44a4_8977_1c0859414274
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_dd73cac9_b90d_44a4_8977_1c0859414274
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:42:47.36683+00:00
-- url     : https://prove2.me/theorems/85642ff6-6772-43b4-b1f6-3db7ecf9f9bf
-- title:
--   A finite maximal drawable supergraph exists
-- statement:
--   On a finite vertex type, every graph with a crossing-free drawing has a drawable supergraph that is maximal under inclusion among drawable graphs on the same vertices. Maximize the edge count over the finite set of possible supergraphs; any proper extension would have strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_dd73cac9_b90d_44a4_8977_1c0859414274
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
