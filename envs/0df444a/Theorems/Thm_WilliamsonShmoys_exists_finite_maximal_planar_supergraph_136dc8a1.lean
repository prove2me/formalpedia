-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_finite_maximal_planar_supergraph_136dc8a1
-- name    : WilliamsonShmoys.exists_finite_maximal_planar_supergraph_136dc8a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:43:27.933989+00:00
-- url     : https://prove2.me/theorems/cb32e0ad-cc14-405b-9341-69f62b49ceed
-- title:
--   Existence of a finite maximal planar supergraph
-- statement:
--   Every graph on a finite ordered vertex type that admits the stated planar drawing has a planar supergraph on the same vertices that is inclusion-maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_finite_maximal_planar_supergraph_136dc8a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V,
          N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
