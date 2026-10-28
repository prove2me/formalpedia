-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count_fcb16b3d
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count_fcb16b3d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:10:45.016285+00:00
-- url     : https://prove2.me/theorems/81c15c9a-2594-42fe-b952-0f3efaac11f9
-- title:
--   Extension of a drawable graph to a planar triangulation
-- statement:
--   Every finite drawable simple graph on at least three vertices is a subgraph of a drawable triangulation on the same vertex type, with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count_fcb16b3d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
