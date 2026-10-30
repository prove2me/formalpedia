-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_triangulation_extension_baad2582_408f_4cf5_91c1_4db79dadb6d2
-- name    : WilliamsonShmoys.planar_drawing_euler_triangulation_extension_baad2582_408f_4cf5_91c1_4db79dadb6d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:30:37.377994+00:00
-- url     : https://prove2.me/theorems/33e090ed-3374-479f-acaf-4f83d536e633
-- title:
--   Euler-count planar extension on the same vertex set
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_triangulation_extension_baad2582_408f_4cf5_91c1_4db79dadb6d2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
