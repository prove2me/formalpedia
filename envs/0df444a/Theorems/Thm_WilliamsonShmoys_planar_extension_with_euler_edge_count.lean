-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_with_euler_edge_count
-- name    : WilliamsonShmoys.planar_extension_with_euler_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:58:36.670646+00:00
-- url     : https://prove2.me/theorems/9367f2ac-e8a7-4ca2-9515-83e5ed53886a
-- title:
--   Planar extension with Euler edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type whose number of edges is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_with_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
