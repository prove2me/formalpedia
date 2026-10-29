-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:06:22.060373+00:00
-- url     : https://prove2.me/theorems/77d992d1-e46c-4955-8948-56b465cd203a
-- title:
--   Every drawable graph has a triangulating extension
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulating_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
