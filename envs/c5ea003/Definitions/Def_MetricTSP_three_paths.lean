-- Prove2me | Definitions.Def_MetricTSP_three_paths
-- name    : MetricTSP_three_paths
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-24T20:11:21.519145+00:00
-- url     : https://prove2.me/theorems/c319c98b-e4c2-4738-ac32-4a3156a63f7f
-- title:
--   The three-parallel-paths integrality-gap family
-- statement:
--   The classical family of graph-metric instances whose integrality gap for the subtour-elimination (Held--Karp) relaxation tends to $4/3$.
--
--   The instance with parameter $k$ has $n = 3k+2$ cities: two hubs $s$ and $t$, and three internally disjoint paths of $k$ internal cities each joining $s$ to $t$. All graph edges have length one and the cost `tpCost` is the shortest-path metric of this graph: cities sharing a path are at distance $|\,\mathrm{pos}(u) - \mathrm{pos}(v)\,|$ along it, and cities on different paths connect through one of the hubs, at distance $\min(\mathrm{pos}(u) + \mathrm{pos}(v),\; 2(k{+}1) - \mathrm{pos}(u) - \mathrm{pos}(v))$, where $\mathrm{pos}$ is the position along the path ($0$ at $s$, $k+1$ at $t$).
--
--   The file also defines the classical fractional certificate `tpCert`: weight $1$ on internal path edges, $2/3$ on the six hub edges, and $1/6$ on the six pairs of equal-position cities adjacent to a hub. It is feasible for the subtour-elimination relaxation with objective $3k+3$, while every Hamiltonian tour costs at least $4k+2$ --- so the gap of the family tends to $4/3$.
--
--   **Formalization Note.** Cities are encoded as `Fin (3k+2)` with $s = 0$, $t = 3k+1$, and the internal city at position $i$ of path $p$ at index $1 + pk + (i-1)$; `tpPath` sends hubs to the sentinel value $3$. Distances are natural numbers, cast to $\mathbb{R}$ in `tpCost`.
-- source:
--   M. X. Goemans, Worst-case comparison of valid inequalities for the TSP, Mathematical Programming 69 (1995) 335-349, https://doi.org/10.1007/BF01585563 (Section 4: the 4/3 lower-bound family of three parallel paths and its fractional solution); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Figure 11.4 and Exercise 11.3 (the same family as the worst-known example for the subtour LP).

import Mathlib

namespace MetricTSP

/-! The three-parallel-paths family of graph-metric instances witnessing the `4/3`
integrality-gap lower bound for the subtour-elimination relaxation.

The instance with parameter `k` has `n = 3k + 2` cities: two hubs `s` (index `0`)
and `t` (index `3k + 1`), and three internally disjoint paths of `k` internal
cities each joining `s` to `t` (indices `1 + p*k + (i-1)` for path `p ∈ {0,1,2}`
and position `i ∈ {1,…,k}`). All graph edges have length one and the cost is the
shortest-path metric of this graph. -/

/-- Position of a city along its path: `0` for the hub `s`, `k+1` for the hub `t`,
and `i ∈ {1,…,k}` for the `i`-th internal city of a path. -/
def tpPos (k : ℕ) (v : Fin (3*k+2)) : ℕ :=
  if v.val = 0 then 0 else if v.val = 3*k+1 then k+1 else (v.val - 1) % k + 1

/-- The path of a city: `0`, `1` or `2` for internal cities, and the sentinel `3`
for the two hubs, which lie on all three paths. -/
def tpPath (k : ℕ) (v : Fin (3*k+2)) : ℕ :=
  if v.val = 0 ∨ v.val = 3*k+1 then 3 else (v.val - 1) / k

/-- The shortest-path distance of the three-paths graph: cities sharing a path
(the hubs share all paths) are at distance `|pos u - pos v|`; cities on different
paths connect through one of the hubs, at distance
`min (pos u + pos v) (2(k+1) - pos u - pos v)`. -/
def tpDist (k : ℕ) (u v : Fin (3*k+2)) : ℕ :=
  if tpPath k u = 3 ∨ tpPath k v = 3 ∨ tpPath k u = tpPath k v then
    Nat.dist (tpPos k u) (tpPos k v)
  else
    min (tpPos k u + tpPos k v) (2*(k+1) - (tpPos k u + tpPos k v))

/-- The three-paths instance: the shortest-path metric, as a real cost function. -/
noncomputable def tpCost (k : ℕ) (u v : Fin (3*k+2)) : ℝ := (tpDist k u v : ℝ)

/-- The classical fractional certificate for the three-paths instance: weight `1` on
internal path edges, `2/3` on the six hub edges, and `1/6` on the six pairs joining
equal-position cities adjacent to a hub (position `1` at `s`, position `k` at `t`).
Its Held–Karp objective is `3k + 3`. -/
noncomputable def tpCert (k : ℕ) (u v : Fin (3*k+2)) : ℝ :=
  if tpPath k u = tpPath k v ∧ tpPath k u ≠ 3 ∧ Nat.dist (tpPos k u) (tpPos k v) = 1 then 1
  else if ((tpPath k u = 3 ∧ tpPath k v ≠ 3) ∨ (tpPath k u ≠ 3 ∧ tpPath k v = 3)) ∧
      Nat.dist (tpPos k u) (tpPos k v) = 1 then 2/3
  else if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
      tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then 1/6
  else 0

end MetricTSP


