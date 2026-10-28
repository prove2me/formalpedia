-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_20261027
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:05:39.072307+00:00
-- url     : https://prove2.me/theorems/0c3562ad-069a-4f29-ac6a-0d9e16f6c896
-- title:
--   Existence of a maximal drawable supergraph on a finite vertex type
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph maximal under edge inclusion among drawable graphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    Exists fun Q : SimpleGraph V =>
      (forall {u v}, P.Adj u v -> Q.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn Q /\
      (forall R : SimpleGraph V,
        (forall {u v}, Q.Adj u v -> R.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn R -> R = Q) := by sorry
