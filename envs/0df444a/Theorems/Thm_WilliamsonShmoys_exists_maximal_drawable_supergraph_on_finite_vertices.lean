-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_on_finite_vertices
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_on_finite_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:10:09.255601+00:00
-- url     : https://prove2.me/theorems/93ca6ce1-2dbc-430d-987a-62e29868359f
-- title:
--   Existence of a maximal drawable supergraph on finite vertices
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_on_finite_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) := by sorry
