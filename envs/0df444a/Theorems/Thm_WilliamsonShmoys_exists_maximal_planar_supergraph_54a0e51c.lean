-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_54a0e51c
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_54a0e51c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:35:56.127875+00:00
-- url     : https://prove2.me/theorems/4ec47299-5e43-4029-ad5e-a7f09958128f
-- title:
--   Existence of a maximal planar supergraph for this extension theorem
-- statement:
--   There is a drawable supergraph of L on the same finite vertex type that contains every drawable supergraph of L.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        L.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ M.edgeSet := by sorry
