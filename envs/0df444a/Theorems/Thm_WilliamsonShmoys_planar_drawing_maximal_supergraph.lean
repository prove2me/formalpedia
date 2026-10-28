-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:03:05.640525+00:00
-- url     : https://prove2.me/theorems/43bb28a7-b5a4-41f7-bef4-ff311693fb98
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   Any finite graph with a drawing in the specified sense is contained in a drawable graph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      G ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ H : SimpleGraph V,
        T ≤ H →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H ≤ T := by sorry
