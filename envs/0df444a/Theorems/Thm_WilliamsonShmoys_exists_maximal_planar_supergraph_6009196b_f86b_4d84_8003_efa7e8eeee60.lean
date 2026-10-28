-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_6009196b_f86b_4d84_8003_efa7e8eeee60
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_6009196b_f86b_4d84_8003_efa7e8eeee60
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:46:37.030986+00:00
-- url     : https://prove2.me/theorems/6f89644b-48e4-441b-9651-7128d360ef3d
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph maximal among drawable graphs on that same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_6009196b_f86b_4d84_8003_efa7e8eeee60
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M) ∧
      G.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
