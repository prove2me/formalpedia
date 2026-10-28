-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_fixed_vertex_set
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists_fixed_vertex_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:46:42.361641+00:00
-- url     : https://prove2.me/theorems/80b681a2-7c99-49c4-857c-4066a965889a
-- title:
--   Finite maximal planar supergraph on a fixed vertex set
-- statement:
--   Every finite graph with a crossing-free drawing has a planar supergraph on the same vertex set that is maximal under planar supergraph inclusion. This removes the finite existence and maximization step from the parent. An independent proof route is to maximize edge count over the finite set of simple graphs on V that contain L and have a drawing; a proper extension has strictly more edges. The assertion is valid without the parent’s lower bound, including when V is small.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists_fixed_vertex_set
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V,
        M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M := by sorry
