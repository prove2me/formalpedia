-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_finite_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.exists_finite_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:07:30.640987+00:00
-- url     : https://prove2.me/theorems/e4b30fb2-f2a0-4025-a3ee-1e6ece83ebab
-- title:
--   A drawable graph has a maximal drawable supergraph on its finite vertex set
-- statement:
--   A drawable graph on a finite vertex type is contained in a drawable supergraph maximal under edge inclusion. Choose a drawable supergraph with the greatest finite number of edges; any drawable extension must then be equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_finite_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ {u v}, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V,
        (∀ {u v}, S.Adj u v → T.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by sorry
