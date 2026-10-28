-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:00:33.246935+00:00
-- url     : https://prove2.me/theorems/7cd1985d-dba7-4a0b-920d-771438c3d00d
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on the same vertices. Finiteness lets one maximize the number of edges among drawable supergraphs; a drawable supergraph of a maximizer must have the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_dabb2cbe_7fe3_4213_96ba_204afbbd922b
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V,
        Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y := by sorry
