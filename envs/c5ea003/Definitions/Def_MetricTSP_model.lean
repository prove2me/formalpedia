-- Prove2me | Definitions.Def_MetricTSP_model
-- name    : MetricTSP_model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T02:34:52.72781+00:00
-- url     : https://prove2.me/theorems/af980b08-49fa-4190-adfd-432d4ce489b3
-- title:
--   Metric TSP: tours, optimal cost, and the Held--Karp relaxation
-- statement:
--   The basic model of metric TSP and its subtour-elimination relaxation.
--
--   `IsMetricCost c` says the cost function $c$ on $n$ cities is symmetric, zero on the diagonal, and satisfies the triangle inequality $c(u,w) \le c(u,v) + c(v,w)$; nonnegativity follows, and distinct cities at distance zero are allowed.
--
--   `tourCost c π` is the cost of the tour that visits the cities in the cyclic order $\pi(0), \pi(1), \dots, \pi(n-1)$ and returns to $\pi(0)$, where $\pi$ is an arbitrary permutation of the cities: the sum of the costs of consecutive steps. Every Hamiltonian cycle arises from some ordering $\pi$. `tspOpt c` is the infimum (a minimum, the set being finite and nonempty) of the tour cost over all orderings.
--
--   `IsHeldKarp x` says the fractional edge-weight vector $x$ is a feasible point of the **subtour-elimination (Held--Karp) relaxation**: symmetric with zero diagonal, entries in $[0,1]$, fractional degree two at every city ($\sum_u x(v,u) = 2$), and crossing every nontrivial cut at least twice ($\sum_{u \in S}\sum_{v \notin S} x(u,v) \ge 2$ for every set $S$ of cities other than $\emptyset$ and all of them). `hkValue c` is the **Held--Karp bound**: the infimum of $\frac12 \sum_u \sum_v c(u,v)\,x(u,v)$ over feasible $x$ (the double sum counts each edge twice). For $n \ge 3$ the incidence vector of any tour is feasible; for $n \le 2$ the relaxation is infeasible and `hkValue` takes the junk value $0$, which is why every theorem carries the hypothesis $3 \le n$.
-- source:
--   Dantzig--Fulkerson--Johnson, Solution of a large-scale traveling-salesman problem, Oper. Res. 2 (1954); Held--Karp, The traveling-salesman problem and minimum spanning trees, Oper. Res. 18 (1970); modern treatment: Traub--Vygen, Approximation Algorithms for Traveling Salesman Problems, CUP 2024, Chapters 1-2

import Mathlib

namespace MetricTSP

/-- A **metric cost function** on `n` cities: symmetric, zero on the diagonal,
and satisfying the triangle inequality. Nonnegativity off the diagonal follows
(`0 = c u u ≤ c u v + c v u = 2 * c u v`). Distinct cities at distance zero are
allowed, as is standard for metric TSP. -/
def IsMetricCost {n : ℕ} (c : Fin n → Fin n → ℝ) : Prop :=
  (∀ u v, c u v = c v u) ∧ (∀ v, c v v = 0) ∧
  ∀ u v w, c u w ≤ c u v + c v w

/-- The cost of the **tour** that visits the cities in the cyclic order
`π 0, π 1, …, π (n-1)` and returns to `π 0`: the ordering is an arbitrary
permutation `π`, and `finRotate n` sends each position to the next one
cyclically. Every Hamiltonian cycle arises from some ordering `π`. -/
noncomputable def tourCost {n : ℕ} (c : Fin n → Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, c (π i) (π (finRotate n i))

/-- The **optimal tour cost**: the infimum of `tourCost c π` over all
orderings `π` of the `n` cities. The set is a nonempty finite set of reals,
so the infimum is attained. -/
noncomputable def tspOpt {n : ℕ} (c : Fin n → Fin n → ℝ) : ℝ :=
  sInf {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = tourCost c π}

/-- A **feasible point of the subtour-elimination (Held–Karp) relaxation**:
a symmetric edge-weight vector `x` with zero diagonal and entries in `[0,1]`,
degree `2` at every city (`∑ u, x v u = 2`), and crossing every nontrivial
cut at least twice: for every set `S` of cities other than `∅` and the whole
city set, `∑ u ∈ S, ∑ v ∉ S, x u v ≥ 2`. -/
def IsHeldKarp {n : ℕ} (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ u v, x u v = x v u) ∧ (∀ v, x v v = 0) ∧
  (∀ u v, 0 ≤ x u v) ∧ (∀ u v, x u v ≤ 1) ∧
  (∀ v, ∑ u, x v u = 2) ∧
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, x u v

/-- The **Held–Karp bound**: the infimum of the objective
`(1/2) * ∑ u, ∑ v, c u v * x u v` (each edge is counted twice in the double
sum) over all feasible points of the subtour-elimination relaxation. For
`n ≥ 3` the incidence vector of any tour is feasible, so the infimum is over
a nonempty set bounded below by `0`. -/
noncomputable def hkValue {n : ℕ} (c : Fin n → Fin n → ℝ) : ℝ :=
  sInf {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
    t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}

end MetricTSP


