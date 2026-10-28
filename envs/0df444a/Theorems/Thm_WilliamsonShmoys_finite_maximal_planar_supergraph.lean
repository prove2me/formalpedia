-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:48:18.992502+00:00
-- url     : https://prove2.me/theorems/3d7bf3b3-5a16-4ff4-b288-c1871907aa31
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable simple graph on a finite vertex type is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph. This is a finite maximization statement and does not require at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
