-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_by_inclusion_79bba284
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal_by_inclusion_79bba284
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:19:36.780401+00:00
-- url     : https://prove2.me/theorems/750a05b2-24ff-4745-9b7b-6fc610b9b5c0
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that is maximal under edge inclusion. The proof route is finite maximization: choose a drawable supergraph with maximum edge count, and use strict growth of edge count under strict edge inclusion to establish maximality. This removes the existence and maximality step from the parent. The finite graph universe and nonempty candidate family, witnessed by K, are the main formal details.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal_by_inclusion_79bba284
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by sorry
