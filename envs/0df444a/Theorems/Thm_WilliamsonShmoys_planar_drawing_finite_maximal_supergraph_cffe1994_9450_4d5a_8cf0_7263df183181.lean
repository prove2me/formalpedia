-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_supergraph_cffe1994_9450_4d5a_8cf0_7263df183181
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_cffe1994_9450_4d5a_8cf0_7263df183181
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:12:38.140203+00:00
-- url     : https://prove2.me/theorems/1e6dcf4f-9be2-4812-b91e-bbeb8cbe4529
-- title:
--   Existence of a maximal drawable supergraph on a finite vertex type
-- statement:
--   A finite drawable graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion. The proof chooses a drawable supergraph with the largest edge set among the finitely many simple graphs on V; the bound on |V| is harmless for this existence step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_cffe1994_9450_4d5a_8cf0_7263df183181
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V =>
      G <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall N : SimpleGraph V,
        M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N ->
        N = M) := by sorry
