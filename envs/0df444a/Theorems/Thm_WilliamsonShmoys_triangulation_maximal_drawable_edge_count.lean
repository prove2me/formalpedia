-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_maximal_drawable_edge_count
-- name    : WilliamsonShmoys.triangulation_maximal_drawable_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:02:05.789224+00:00
-- url     : https://prove2.me/theorems/b97bc774-c2a6-4439-a9a2-ba000310ef41
-- title:
--   Maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices with no drawable proper supergraph on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_maximal_drawable_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
