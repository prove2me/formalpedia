-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- name    : WilliamsonShmoys.planar_triangulation_extension_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:13:56.057596+00:00
-- url     : https://prove2.me/theorems/391f3239-9f51-4455-9b2f-cbbc61103aca
-- title:
--   Extension of a planar drawing to a triangulation
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
