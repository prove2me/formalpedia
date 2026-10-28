-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_triangulation
-- name    : WilliamsonShmoys.planar_drawing_extension_to_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:35:37.098737+00:00
-- url     : https://prove2.me/theorems/59af219e-53d5-4bc3-9f66-d0ff3ecbbbf9
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Any drawable simple graph on a fixed finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extension_to_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      N.edgeSet ⊆ P.edgeSet ∧
      P.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
