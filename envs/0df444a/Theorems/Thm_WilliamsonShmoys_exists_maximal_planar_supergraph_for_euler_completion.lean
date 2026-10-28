-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_euler_completion
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_euler_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:50:36.233752+00:00
-- url     : https://prove2.me/theorems/6b98c527-4c91-44c8-9ad2-d9d624195909
-- title:
--   Existence of a maximal planar supergraph for Euler completion
-- statement:
--   A planar graph on a finite ordered vertex type has a planar supergraph on that same type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_euler_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      (forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) := by sorry
