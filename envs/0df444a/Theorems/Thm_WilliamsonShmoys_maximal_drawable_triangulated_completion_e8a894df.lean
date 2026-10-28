-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulated_completion_e8a894df
-- name    : WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:41:46.96081+00:00
-- url     : https://prove2.me/theorems/202d559d-0e5c-40b5-aae4-a86f170ee5dd
-- title:
--   Triangulated completion of a drawable graph
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable triangulated supergraph on the same vertex set, whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
