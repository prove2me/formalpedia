-- Prove2me | Definitions.Def_LinearOptimization_Cut
-- name    : LinearOptimization_Cut
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:35:55.807266+00:00
-- url     : https://prove2.me/theorems/430631f0-82b1-4ab6-9e6b-d89166554541
-- title:
--   $s$-$t$ cut and its capacity
-- statement:
--   **(Cuts, Bertsimas & Tsitsiklis, §7.5, p. 309 — defined in running text, not a numbered definition)** We define an $s$-$t$ cut as a subset $S$ of the set of nodes $\mathcal{N}$, such that $s\in S$ and $t\notin S$; in our context the nodes $s$ and $t$ are fixed, and we refer to $S$ as simply a *cut*.
--
--   We define the *capacity* $C(S)$ of a cut $S$ as the sum of the capacities of the arcs that cross from $S$ to its complement, that is,
--
--   $$C(S)=\sum_{\{(i,j)\in\mathcal{A}\,\mid\, i\in S,\ j\notin S\}} u_{ij}.$$
--
--   Any flow from $s$ to $t$ must at some point cross an arc $(i,j)$ with $i\in S$ and $j\notin S$; for this reason, the value $v$ of any feasible flow satisfies
--
--   $$v\le C(S)$$
--
--   for every cut (Eq. (7.14), p. 310).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §7.5, 'Cuts', pp. 309-310

import Definitions.Def_LinearOptimization_MaxFlowProblem

/-!
Cuts and their capacities.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §7.5 "Cuts" (pp. 309–310) — an *unnumbered*
running-text definition: an `s`-`t` *cut* is a subset `S` of the node set
`𝒩` such that `s ∈ S` and `t ∉ S` (with `s`, `t` fixed we refer to `S`
simply as a cut); the *capacity* `C(S)` of a cut `S` is the sum of the
capacities of the arcs that cross from `S` to its complement:
`C(S) = ∑_{(i,j) ∈ 𝒜 : i ∈ S, j ∉ S} uᵢⱼ`.

Any flow from `s` to `t` must at some point cross an arc from `S` to its
complement; for this reason the value `v` of any feasible flow satisfies
`v ≤ C(S)` for every cut (Eq. (7.14), p. 310) — the weak-duality warm-up,
subsumed by `max_flow_min_cut` and not a separate item.

Design: `S` is a `Finset (Fin n)` (decidable membership for the crossing
sum); the capacity is an `ℝ≥0∞` sum, possibly `⊤`.
-/

open Matrix
open scoped ENNReal

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §7.5 (p. 309).** An `s`-`t` cut: a set `S` of nodes with
`s ∈ S` and `t ∉ S`. -/
def IsCut {n : ℕ} (s t : Fin n) (S : Finset (Fin n)) : Prop :=
  s ∈ S ∧ t ∉ S

/-- **Bertsimas & Tsitsiklis, §7.5 (p. 309).** The capacity `C(S)` of the cut `S`: the sum of
the capacities of the arcs whose start node is in `S` and whose end node
is not (an `ℝ≥0∞` sum, possibly `⊤`). -/
noncomputable def cutCapacity {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (S : Finset (Fin n)) : ℝ≥0∞ :=
  ∑ k, if (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S then u k else 0

end LinearOptimization


