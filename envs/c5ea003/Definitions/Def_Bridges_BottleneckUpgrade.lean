-- Prove2me | Definitions.Def_Bridges_BottleneckUpgrade
-- name    : Bridges_BottleneckUpgrade
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:24:45.099442+00:00
-- url     : https://prove2.me/theorems/467672a2-6114-42d4-a6eb-d40084d92e27
-- title:
--   Aether Catalog definitions — Bridges_BottleneckUpgrade
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BottleneckUpgrade`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BottleneckUpgrade.lean by skeleton subtraction
import Mathlib
/-
# Certified Bottleneck Upgrade Theorems

A cross-domain capacity improvement calculus: in finite systems whose global
performance equals the infimum of local capacities, a targeted upgrade on the
critical (argmin) set produces a provable, exact throughput gain.

Applications:
- **Infrastructure**: road/rail corridor throughput
- **Manufacturing**: serial production line cycle-time
- **Telecommunications**: end-to-end link capacity

The key insight is that upgrading every component at the minimum capacity by
one unit raises the system minimum by exactly one, provided all non-critical
components were already strictly above the old minimum.
-/


open Finset

/-! ## Core definitions -/

/-- The bottleneck set: elements of `s` achieving the minimum capacity. -/
def bottleneckSet {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℕ) (hs : s.Nonempty) : Finset α :=
  s.filter (fun x => c x = s.inf' hs c)

/-- Raise the capacity function by `δ` on elements of `u`. -/
def raiseOn {α : Type*} [DecidableEq α]
    (u : Finset α) (δ : ℕ) (c : α → ℕ) : α → ℕ :=
  fun x => c x + if x ∈ u then δ else 0

/-- Unit upgrade on a set: add 1 to every element of `u`. -/
def unitUpgradeOn {α : Type*} [DecidableEq α]
    (u : Finset α) (c : α → ℕ) : α → ℕ :=
  fun x => c x + if x ∈ u then 1 else 0

/-! ## Helper lemmas -/






/-! ## Main theorem: exact one-step bottleneck improvement -/

/-
**Bottleneck Upgrade Theorem (Exact Form).**
If `critical` is exactly the argmin set of `c` over `s`, all non-critical elements
have capacity at least `min + 1`, and `c'` upgrades each critical element to exactly
`c x + 1` while keeping all others unchanged, then the new minimum equals
the old minimum plus 1.
-/

/-
**Bottleneck Upgrade Theorem (Inequality Form).**
Under the same conditions but with `c' x ≥ c x + 1` on the critical set,
we get a lower bound on the new minimum.
-/

/-! ## Canonical form using `raiseOn` and `bottleneckSet` -/

/-
**Canonical Bottleneck Raise Theorem.**
Raising the bottleneck set by 1 increases the system minimum by exactly 1,
provided all non-bottleneck elements are strictly above the current minimum.
-/

/-! ## Optimality theorem: bottleneck upgrades are optimal -/

/-
**Budgeted Optimality Theorem.**
Among all unit upgrade plans of equal cardinality, upgrading the bottleneck set
maximizes (or ties for maximum of) the new system minimum.
-/

/-! ## Domain-specific corollaries -/




/-! ## Verification: axiom check -/


