-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_triangulation
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:48:25.012711+00:00
-- url     : https://prove2.me/theorems/8440c584-79dd-4e07-8218-fa1f87692d7a
-- title:
--   Extension to a maximal triangulation on fixed vertices
-- statement:
--   Every crossing-free drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable graphs and has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
