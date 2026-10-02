-- Prove2me | Theorems.Thm_BookSixth_crossing_lemma
-- name    : BookSixth.crossing_lemma
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:37:16.619744+00:00
-- url     : https://prove2.me/theorems/634d53d7-5229-4fc2-9b69-d155a2613bce
-- title:
--   Chapter 45, Theorem 4: crossing lemma (drawing form)
-- statement:
--   Every good drawing of a finite simple graph with N positive vertices and M at least 4N edges has at least M³/(64N²) interior crossing points. Edges are continuous injective arcs; interiors avoid vertices, adjacent edges do not cross, and no three edge interiors meet at one point. The finite crossing set is required to record exactly all pairwise interior intersections. This universally quantified drawing form applies in particular to a crossing-minimizing good drawing; no numerical bound is assumed in the drawing interface.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4: crossing lemma (drawing form), p. 317. https://doi.org/10.1007/978-3-662-57265-8_45

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.crossing_lemma {N M : ℕ} (hN : 0 < N) (hM : 4*N ≤ M) (D : PlaneDrawing N M) :
    M^3 ≤ 64 * N^2 * D.crossings.card := by sorry
