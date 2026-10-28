-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:20:19.450047+00:00
-- url     : https://prove2.me/theorems/494f19c2-36d6-415b-b118-d6e708262cb2
-- title:
--   Every planar graph has a maximal planar extension on the same vertices
-- statement:
--   Any finite planar graph has a planar supergraph on the same vertices that is maximal under inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  sorry
