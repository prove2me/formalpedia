-- Prove2me | Theorems.Thm_Hirsch_near_geodesic_occurrence_carrier_budget
-- name    : Hirsch.near_geodesic_occurrence_carrier_budget
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T23:23:56.280649+00:00
-- url     : https://prove2.me/theorems/79bdd301-35e1-4cdb-a6ed-eb49b00e5c3c
-- title:
--   Near-geodesic occurrence windows bound joint carrier resources
-- statement:
--   A graph walk at most q edges above endpoint distance has at most q+3
--   closed-neighborhood contact positions with any fixed vertex. Count occurrence
--   positions, including repeated labels, and double-count contacts with any finite
--   available set. If each selected position satisfies the explicit pointwise
--   integer resource inequality, the total resource obeys the stated joint bound.
--   At full availability e=|A| the mass is at most (q+3)|A|.
--   This is a graph/resource theorem, not an unconditional polytope diameter bound.
--   The geometric portal-debt and simple-polytope interpretations are separate.
-- source:
--   Graph shortcut and double-counting proof; https://github.com/jjoshua2/prove2me-work/tree/35dc985f0736e6ca612f747dcc45d6f528c3d62f

import Mathlib
open scoped BigOperators
open Set

theorem Hirsch.near_geodesic_occurrence_carrier_budget {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length) (delta : ℕ → ℕ) (e : ℕ)
    (hbudget : ∀ k ∈ positions, delta k + available.card ≤ e +
      (available.filter (fun z => z = p.getVert k ∨ G.Adj z (p.getVert k))).card) :
    (∑ k ∈ positions, delta k) + positions.card * available.card ≤
      positions.card * e + (q+3)*available.card := by sorry
