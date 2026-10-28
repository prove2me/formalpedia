-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_98108dba_1927_4e81_b6e3_ce95ad278038
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_98108dba_1927_4e81_b6e3_ce95ad278038
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:16:17.825136+00:00
-- url     : https://prove2.me/theorems/725630e7-fd9d-4d7e-aef0-7ba7f56e6fde
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertex type. Maximize edge-set cardinality among drawable supergraphs of the original graph; finiteness gives a maximizer, and a strict extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_98108dba_1927_4e81_b6e3_ce95ad278038
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
