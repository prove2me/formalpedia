-- Prove2me | Theorems.Thm_bottleneck_set_is_optimal_for_one_step_throughput
-- name    : bottleneck_set_is_optimal_for_one_step_throughput
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:35:13.822891+00:00
-- url     : https://prove2.me/theorems/d39fedc3-272a-4c21-9e32-9a2c0843b30a
-- title:
--   Bottleneck set is optimal for one step throughput
-- statement:
--   Formal statement of `bottleneck_set_is_optimal_for_one_step_throughput` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem bottleneck_set_is_optimal_for_one_step_throughput    {α : Type*} [DecidableEq α]
--       (s u : Finset α) (c : α → ℕ) (hs : s.Nonempty)
--       (_hu : u ⊆ s)
--       (hcard : u.card = (bottleneckSet s c hs).card) :
--       s.inf' hs (unitUpgradeOn u c) ≤
--         s.inf' hs (unitUpgradeOn (bottleneckSet s c hs) c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BottleneckUpgrade.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BottleneckUpgrade.lean#L162

-- Thm stub generated from Bridges/BottleneckUpgrade.lean
import Mathlib
import Definitions.Def_Bridges_BottleneckUpgrade
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


-- open removed: section is not a namespace

/-! ## Core definitions -/




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

theorem bottleneck_set_is_optimal_for_one_step_throughput    {α : Type*} [DecidableEq α]
    (s u : Finset α) (c : α → ℕ) (hs : s.Nonempty)
    (_hu : u ⊆ s)
    (hcard : u.card = (bottleneckSet s c hs).card) :
    s.inf' hs (unitUpgradeOn u c) ≤
      s.inf' hs (unitUpgradeOn (bottleneckSet s c hs) c) := by sorry
