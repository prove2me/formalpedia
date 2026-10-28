-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:01:39.231529+00:00
-- url     : https://prove2.me/theorems/838490eb-e96f-472c-99c4-be4f7f6b7cb5
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Any graph with a drawing under the supplied crossing-free drawing definition, on at least three vertices, has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
