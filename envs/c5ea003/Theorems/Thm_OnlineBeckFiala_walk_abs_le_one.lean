-- Prove2me | Theorems.Thm_OnlineBeckFiala_walk_abs_le_one
-- name    : OnlineBeckFiala.walk_abs_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:18:38.494317+00:00
-- url     : https://prove2.me/theorems/595c72c3-0878-496e-aec8-9a011500e587
-- title:
--   Compact support / prefix bound.
-- statement:
--   **Compact support / prefix bound.**  If every increment satisfies `|a t| ≤ 1`,
--   the greedy self-balancing walk never leaves `[-1, 1]`.
--
--   ```lean
--   theorem OnlineBeckFiala.walk_abs_le_one(a : ℕ → ℝ) (ha : ∀ s, |a s| ≤ 1) :
--       ∀ t, |walk a t| ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OnlineBeckFialaWalk.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OnlineBeckFialaWalk.lean#L95

-- Thm stub generated from Novelty/OnlineBeckFialaWalk.lean
import Mathlib
import Definitions.Def_Novelty_OnlineBeckFialaWalk
/-
# The Self-Balancing Walk: Online Prefix Discrepancy in One Dimension

The **Beck–Fiala** line of research studies *discrepancy*: given vectors arriving
one at a time, choose a sign `±1` for each so that every *prefix* of the resulting
signed sum stays small.  The recent work *"Online Beck–Fiala Down to Logarithmic
Sparsity"* builds its high-dimensional algorithm out of a one-dimensional
primitive — a **compactly supported, online, self-balancing walk**.  This file
formalizes that primitive in full.

Concretely, real increments `a 0, a 1, a 2, …` with `|a t| ≤ 1` arrive online.  At
step `t` we must commit to a sign `ε t ∈ {+1, -1}` *depending only on the history*
and on the current increment, forming the running sum
`S t = ∑_{s < t} ε s · a s`.  The greedy rule "push the running sum back toward
`0`" keeps the walk trapped in the compact interval `[-1, 1]` **forever**,
independently of how many increments arrive.

Main results:

* `walk_abs_le_one` — the greedy walk satisfies `|S t| ≤ 1` for every `t`
  (the compact-support / prefix-discrepancy bound).
* `onlineSign_mem` — the committed values really are signs, `ε t = 1 ∨ ε t = -1`.
* `walk_eq_sum` — the greedy walk equals the online signed prefix sum
  `∑_{s < t} ε s · a s`, certifying that the bound is about a genuine `±1` coloring.
* `prefix_discrepancy_le_one` — combining the two: the online signed prefix sums
  all have absolute value `≤ 1`.
* `exists_signs_prefix_le_one` — hence a sign sequence keeping every prefix within
  `[-1, 1]` *exists* (the offline consequence).
* `online_prefix_lower_bound` — `1` is optimal: on the all-ones stream every online
  strategy already incurs prefix discrepancy `≥ 1` at the very first step.
* `walk_abs_le` — the scaled version: increments bounded by `c ≥ 0` give
  `|S t| ≤ c`.
-/

open OnlineBeckFiala

open Finset

theorem OnlineBeckFiala.walk_abs_le_one(a : ℕ → ℝ) (ha : ∀ s, |a s| ≤ 1) :
    ∀ t, |walk a t| ≤ 1 := by sorry
