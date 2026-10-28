-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_for_edge_count_64cb9f36
-- name    : WilliamsonShmoys.exists_maximal_extension_for_edge_count_64cb9f36
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:38:20.409935+00:00
-- url     : https://prove2.me/theorems/1de99c26-b80c-4c2f-8cb4-4dee96483a7c
-- title:
--   A planar drawing has an edge-maximal planar supergraph
-- statement:
--   Every finite drawn planar graph is contained in a planar graph on the same vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_for_edge_count_64cb9f36
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V,
        P.edgeSet ⊂ Q.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn Q := by sorry
