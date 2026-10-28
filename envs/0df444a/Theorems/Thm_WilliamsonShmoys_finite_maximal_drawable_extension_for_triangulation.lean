-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_extension_for_triangulation
-- name    : WilliamsonShmoys.finite_maximal_drawable_extension_for_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:35:15.752505+00:00
-- url     : https://prove2.me/theorems/717f9cc0-b3bb-439b-bf81-fbfeb2632c28
-- title:
--   Finite maximal drawable extension for triangulation
-- statement:
--   Every drawable graph on a fixed finite vertex type has a drawable supergraph maximal under graph inclusion. This is obtained by maximizing the number of edges over the finite set of drawable supergraphs containing the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_extension_for_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X := by sorry
