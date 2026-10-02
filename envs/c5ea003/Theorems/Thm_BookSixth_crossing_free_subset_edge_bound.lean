-- Prove2me | Theorems.Thm_BookSixth_crossing_free_subset_edge_bound
-- name    : BookSixth.crossing_free_subset_edge_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T13:00:02.070535+00:00
-- url     : https://prove2.me/theorems/b2255bec-31ff-4bf9-84b4-81705574eaac
-- title:
--   Planar edge bound for a crossing-free subset of a good drawing
-- statement:
--   Let D be a good drawing of a finite simple graph in the real plane. Let V be any subset of its labeled vertices and E any subset of its labeled edges. Suppose every edge in E has both endpoints in V and distinct edges in E have disjoint interiors. Then
--
--   $$|E| \le 3|V|.$$
--
--   The estimate includes empty vertex and edge sets, disconnected graphs, and isolated vertices. It concerns the actual continuous injective arcs of the drawing, not an assumed combinatorial embedding. This is the geometric input to the crossing lemma after edges meeting at recorded interior crossings have been removed.
-- source:
--   Derived weak form of the planar simple-graph edge estimate used in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. Parent: BookSixth.drawing_sampling_bound (6968bb2a-7af8-400f-bc59-39aa35d6ea0d). For at least three vertices the usual estimate is |E| <= 3|V|-6; the displayed weak bound also covers the smaller cases. The subset formulation is a derived intermediate statement, not a separately numbered book theorem.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.crossing_free_subset_edge_bound {N M : ℕ} (D : PlaneDrawing N M)
    (V : Finset (Fin N)) (E : Finset (Fin M))
    (hend : ∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V)
    (hfree : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
      0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
      D.arc e t ≠ D.arc f s) :
    E.card ≤ 3 * V.card := by sorry
