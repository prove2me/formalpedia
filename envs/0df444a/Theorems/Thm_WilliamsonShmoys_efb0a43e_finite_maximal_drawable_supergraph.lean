-- Prove2me | Theorems.Thm_WilliamsonShmoys_efb0a43e_finite_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.efb0a43e_finite_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:41:32.516957+00:00
-- url     : https://prove2.me/theorems/e3aaf02a-6294-485b-b9c1-9f06cff57eb4
-- title:
--   A finite maximal drawable supergraph exists
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that admits no proper drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.efb0a43e_finite_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
