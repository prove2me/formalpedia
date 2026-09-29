-- Prove2me | Definitions.Def_Novelty_OnlineBeckFialaWalk
-- name    : Novelty_OnlineBeckFialaWalk
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:36.353464+00:00
-- url     : https://prove2.me/theorems/ca4cbc11-091b-4ed0-9a8d-734d04b0975f
-- title:
--   Aether Catalog definitions — Novelty_OnlineBeckFialaWalk
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OnlineBeckFialaWalk`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OnlineBeckFialaWalk.lean by skeleton subtraction
import Mathlib
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

namespace OnlineBeckFiala

open Finset

/-- The **greedy self-balancing walk** driven by the increment stream `a`.

`walk a t` is the running sum after processing `a 0, …, a (t-1)`.  At each step we
add `|a t|` if the current sum is `≤ 0`, and subtract `|a t|` otherwise — i.e. we
choose the sign that pushes the running sum back toward `0`.  The step depends only
on the past (`walk a t`) and the current increment `a t`, so the rule is *online*. -/
noncomputable def walk (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (t + 1) => walk a t + (if walk a t ≤ 0 then |a t| else -|a t|)



/-- The **online sign** committed to at step `t`: it multiplies the true increment
`a t`, and is `+1` or `-1` depending on the greedy rule and the sign of `a t`. -/
noncomputable def onlineSign (a : ℕ → ℝ) (t : ℕ) : ℝ :=
  (if walk a t ≤ 0 then (1 : ℝ) else -1) * (if 0 ≤ a t then (1 : ℝ) else -1)










end OnlineBeckFiala


