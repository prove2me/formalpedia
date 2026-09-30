-- Prove2me | Theorems.Thm_Hirsch_geodesic_joint_budget_of_all_available_contacts
-- name    : Hirsch.geodesic_joint_budget_of_all_available_contacts
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T22:50:57.157785+00:00
-- url     : https://prove2.me/theorems/b8f45079-9784-43a0-b659-0914a2038332
-- title:
--   All available vertices give a joint budget along a graph geodesic
-- statement:
--   Let p be a metric-shortest path in an undirected simple graph. Let A be
--   any finite set of available vertices, including vertices off the path, and let
--   L be a duplicate-free list of vertices on p. Suppose each selected vertex i
--   has a nonnegative integer budget delta_i satisfying
--   delta_i + |A| <= e + #{j in A : j=i or j is adjacent to i}.
--   Then sum_i delta_i + |L|*|A| <= |L|*e + 3|A|.
--   In particular when |A|=e the total budget is at most 3e.
--
--   Each available vertex contacts a window of at most three path positions:
--   otherwise it supplies a two-edge shortcut. Double-count those contacts and
--   sum the pointwise inequalities. True metric shortestness is essential.
--   This theorem is a graph and integer-budget statement. The separate repository
--   adapter proves its applicability to actual clipping carrier excesses; the
--   statement itself neither identifies delta with edge distance nor resolves
--   the Polynomial Hirsch conjecture.
-- source:
--   Geodesic shortcut and double-counting formalization, https://github.com/jjoshua2/prove2me-work/tree/21b4413f294d4503aa98b2c0ded939595724108e

import Mathlib
open scoped BigOperators
open Set

theorem Hirsch.geodesic_joint_budget_of_all_available_contacts {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (available : Finset V) (labels : List V) (hnd : labels.Nodup)
    (hsub : ∀ i ∈ labels, i ∈ p.support) (delta : V → ℕ) (e : ℕ)
    (hbudget : ∀ i ∈ labels, delta i + available.card ≤ e +
      (available.filter (fun j => j = i ∨ G.Adj j i)).card) :
    (labels.map delta).sum + labels.length * available.card ≤
      labels.length * e + 3 * available.card := by sorry
