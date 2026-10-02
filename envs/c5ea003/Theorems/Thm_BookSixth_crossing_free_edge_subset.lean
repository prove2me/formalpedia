-- Prove2me | Theorems.Thm_BookSixth_crossing_free_edge_subset
-- name    : BookSixth.crossing_free_edge_subset
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:05:07.09712+00:00
-- url     : https://prove2.me/theorems/f6b5e29c-cda8-46be-aa03-f0cf2083f729
-- title:
--   Deleting at most one edge per crossing leaves disjoint interiors
-- statement:
--   Let D be a good plane drawing with M labeled edges and C recorded interior intersections. There is a set E of retained edges satisfying
--
--   $$M \le |E|+C,$$
--
--   whose distinct edges have pairwise disjoint interiors. Thus all interior intersections can be eliminated by deleting at most C edges.
--
--   This is the deletion step in the planar edge estimate used by the crossing lemma. It makes no claim about the number of edges in a crossing-free drawing and does not assume Euler's formula.
-- source:
--   Derived intermediate lemma for BookSixth.drawing_sampling_bound (6968bb2a-7af8-400f-bc59-39aa35d6ea0d) and BookSixth.crossing_lemma (634d53d7-5229-4fc2-9b69-d155a2613bce). Parent source: Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. This derived statement follows directly from the published PlaneDrawing.crossings_exact field: remove the first edge in each crossing record. It is not a quotation of a separately numbered result.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.crossing_free_edge_subset {N M : ℕ} (D : PlaneDrawing N M) :
    ∃ E : Finset (Fin M), M ≤ E.card + D.crossings.card ∧
      ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
        0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
        D.arc e t ≠ D.arc f s := by sorry
