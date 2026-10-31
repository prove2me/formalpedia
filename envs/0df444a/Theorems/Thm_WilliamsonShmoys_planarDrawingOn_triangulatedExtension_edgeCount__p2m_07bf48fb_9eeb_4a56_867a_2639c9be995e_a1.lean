-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulatedExtension_edgeCount__p2m_07bf48fb_9eeb_4a56_867a_2639c9be995e_a1
-- name    : WilliamsonShmoys.planarDrawingOn_triangulatedExtension_edgeCount__p2m_07bf48fb_9eeb_4a56_867a_2639c9be995e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:29.259903+00:00
-- url     : https://prove2.me/theorems/998ffb22-8369-4943-b685-9f335822785c
-- title:
--   Triangulated extension and exact planar edge count
-- statement:
--   Every finite drawable simple graph with at least three vertices is contained, on the same vertex set, in a drawable simple graph whose edge count is exactly 3|V|−6; the extension has at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_triangulatedExtension_edgeCount__p2m_07bf48fb_9eeb_4a56_867a_2639c9be995e_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ T : SimpleGraph V, M.edgeSet.ncard ≤ T.edgeSet.ncard ∧ HasPlanarDrawingOn T ∧ T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
