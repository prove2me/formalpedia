-- Prove2me | Theorems.Thm_planar_drawing_edgeSet_ncard_le_three_mul_card_sub_six
-- name    : planar_drawing_edgeSet_ncard_le_three_mul_card_sub_six
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:39:28.604352+00:00
-- url     : https://prove2.me/theorems/220157de-5c6a-4675-95e0-4543900f39c4
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the classical planar edge bound; a proof route extracts a plane embedding from the drawing and applies Euler's formula, accounting for components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planar_drawing_edgeSet_ncard_le_three_mul_card_sub_six
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
