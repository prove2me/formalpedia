-- Prove2me | Theorems.Thm_menger_directed_max_flow
-- name    : menger_directed_max_flow
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:45:17.057203+00:00
-- url     : https://prove2.me/theorems/10d5bb20-e580-4b9b-82d2-395da456f8ef
-- statement:
--   Max-flow min-cut theorem (Ford-Fulkerson): The maximum flow from s to t in a network equals the minimum cut capacity. Proved. Here formalized with integer capacities and flows.
-- source:
--   https://en.wikipedia.org/wiki/Max-flow_min-cut_theorem

import Mathlib

import Mathlib

theorem menger_directed_max_flow (n : ℕ) (hn : 1 ≤ n)
    (capacity : Fin n → Fin n → ℕ)
    (s t : Fin n) (hst : s ≠ t) :
    ∃ (max_flow : ℕ),
      (∃ flow : Fin n → Fin n → ℕ,
        (∀ u v, flow u v ≤ capacity u v) ∧
        (∀ u, u ≠ s → u ≠ t → ∑ v, flow u v = ∑ v, flow v u) ∧
        max_flow = ∑ v, flow s v) ∧
      (∀ (S : Finset (Fin n)), s ∈ S → t ∉ S →
        max_flow ≤ ∑ u ∈ S, ∑ v ∉ S, capacity u v) := by
  sorry
