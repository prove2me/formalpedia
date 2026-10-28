-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_exists_for_edge_bound
-- name    : WilliamsonShmoys.planar_extension_exists_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:13:51.165303+00:00
-- url     : https://prove2.me/theorems/472ca3e1-3cd4-4002-a04a-f1545bb82ec5
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under drawable extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_exists_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        (∀ ⦃u v⦄, M.Adj u v → N.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
