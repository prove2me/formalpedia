-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_6274f47d
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_6274f47d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:06:02.17283+00:00
-- url     : https://prove2.me/theorems/003ea3a1-311c-4981-a04f-5bda7633b7ed
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs. Finiteness of the possible edge sets gives an independent proof route by maximizing the edge set among drawable extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_6274f47d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M.edgeSet ⊆ N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet = M.edgeSet := by sorry
