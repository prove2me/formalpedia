-- Prove2me | Theorems.Thm_BookSixth_drawing_sampling_bound
-- name    : BookSixth.drawing_sampling_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T11:35:49.471122+00:00
-- url     : https://prove2.me/theorems/6968bb2a-7af8-400f-bc59-39aa35d6ea0d
-- title:
--   Vertex-sampling inequality for a good plane drawing
-- statement:
--   Let D be a good drawing of a finite simple graph with N vertices, M edges, and C recorded interior intersections. For every real number p with 0 ≤ p ≤ 1,
--
--   $$p^2 M \le 3pN+p^4C.$$
--
--   This intermediate inequality isolates the planar edge estimate and independent vertex sampling from the algebraic optimization in the crossing lemma. It applies also to empty drawings and to the endpoints p=0 and p=1.
-- source:
--   Intermediate lemma for BookSixth.crossing_lemma (634d53d7-5229-4fc2-9b69-d155a2613bce), whose source is Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. Derived formulation: apply the planar deletion bound to independently sampled vertices and use the two distinct endpoints of every edge and four distinct endpoints of every crossing. This is an intermediate formalization statement, not a quotation of a separately numbered result.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.drawing_sampling_bound {N M : ℕ} (D : PlaneDrawing N M) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : p^2 * (M : ℝ) ≤ 3*p*(N : ℝ) + p^4*(D.crossings.card : ℝ) := by sorry
