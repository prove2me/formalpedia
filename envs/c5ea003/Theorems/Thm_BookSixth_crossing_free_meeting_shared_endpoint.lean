-- Prove2me | Theorems.Thm_BookSixth_crossing_free_meeting_shared_endpoint
-- name    : BookSixth.crossing_free_meeting_shared_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:49:44.400628+00:00
-- url     : https://prove2.me/theorems/6deab9ed-ec26-41ca-b518-f5d82d7e524a
-- title:
--   Crossing-free arc meetings occur at shared endpoints
-- statement:
--   Let D be a good drawing with continuous injective edge arcs whose interiors avoid nonincident vertices. If the arcs of two edges e and f have disjoint interiors and yet D.arc e t = D.arc f s for some parameters, then the meeting point is a vertex shared by both edges: there is v with v an endpoint of e and of f and D.arc e t = D.vertex v. Reduction component for parent BookSixth.crossing_free_subset_edge_bound (b2255bec-31ff-4bf9-84b4-81705574eaac): it establishes that crossing-free arcs meet only at endpoints, the interface fact needed before any Euler or face-counting argument can be attached to the drawing.
-- source:
--   Interface consequence of the good-drawing axioms (endpoint interpolation D.start/D.finish, interior vertex avoidance D.avoid_vertices, vertex injectivity D.vertex_injective) for the drawing interface in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45. Reduction component for parent BookSixth.crossing_free_subset_edge_bound (b2255bec-31ff-4bf9-84b4-81705574eaac).

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.crossing_free_meeting_shared_endpoint {N M : ℕ} (D : PlaneDrawing N M) (e f : Fin M) (hfree : ∀ t s : EdgeParameter, 0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 → D.arc e t ≠ D.arc f s) (t s : EdgeParameter) (h : D.arc e t = D.arc f s) : ∃ v : Fin N, (D.left e = v ∨ D.right e = v) ∧ (D.left f = v ∨ D.right f = v) ∧ D.arc e t = D.vertex v := by sorry
