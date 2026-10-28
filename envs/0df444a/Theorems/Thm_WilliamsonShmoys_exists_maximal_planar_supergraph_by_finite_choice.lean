-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_by_finite_choice
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_by_finite_choice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:55:57.082697+00:00
-- url     : https://prove2.me/theorems/9d86ef30-7979-414d-b34d-9943782e8b5f
-- title:
--   Finite choice of a maximal drawable supergraph
-- statement:
--   Choose a drawable supergraph of K with the largest edge set among the finitely many graphs on V; it is inclusion maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_by_finite_choice
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V,
          H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by sorry
