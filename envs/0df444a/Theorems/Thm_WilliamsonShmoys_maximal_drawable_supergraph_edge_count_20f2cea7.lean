-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_20f2cea7
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_count_20f2cea7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:13:08.554337+00:00
-- url     : https://prove2.me/theorems/f13ee4ae-5c3d-4f52-b57e-238bcdb15ebc
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_count_20f2cea7
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
