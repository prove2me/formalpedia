-- Prove2me | Theorems.Thm_MomentHierarchy_orbits_perm_eq_card_setoid
-- name    : MomentHierarchy.orbits_perm_eq_card_setoid
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:36:33.068141+00:00
-- url     : https://prove2.me/theorems/d1604ea0-aa16-4a72-be78-75f773a4daf2
-- title:
--   Orbits on `k`-tuples are set partitions.
-- statement:
--   **Orbits on `k`-tuples are set partitions.** For `k ≤ |X|` the orbits of the full
--   symmetric group on `X^k` are in bijection with the partitions of a `k`-element set.
--
--   ```lean
--   theorem MomentHierarchy.orbits_perm_eq_card_setoid(hk : k ≤ Nat.card X) :
--       Nat.card (orbitRel.Quotient (Equiv.Perm X) (Fin k → X)) = Nat.card (Setoid (Fin k)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/MomentHierarchyBell.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/MomentHierarchyBell.lean#L151

-- Thm stub generated from Logic/MomentHierarchyBell.lean
import Mathlib
import Definitions.Def_Logic_MomentHierarchy
import Definitions.Def_Logic_MomentHierarchyBell

/-!
# The Burnside Moment Hierarchy, part II: symmetric groups, kernels and Bell numbers

This file continues `Logic.MomentHierarchy`. Instantiating the moment identity
`∑_{g ∈ G} |X^g|^k = #((X^k)/G) · |G|` at the full symmetric group `Sym X` turns the
hierarchy into the moment sequence of the number of fixed points of a uniformly random
permutation. The orbits of `Sym X` on `k`-tuples are classified by kernel partitions, so
for `k ≤ |X|` the `k`-th level counts set partitions of a `k`-element set, and the
Cauchy–Schwarz inequality of part I becomes log-convexity of the Bell sequence.
-/

open MulAction Finset

open MomentHierarchy

/-! ## Cycle 4: instantiation at the symmetric group

For the natural action of `Equiv.Perm X` on a finite `X` the hierarchy becomes the
moment sequence of the number of fixed points of a uniformly random permutation. The
action is transitive and 2-transitive, so the first two moments are `1` and `2` — the
first two Bell numbers, i.e. the first two moments of a Poisson(1) variable. -/


variable (X : Type*) [Fintype X] [DecidableEq X]







/-! ## Cycle 5: kernels, set partitions and log-convexity of the Bell sequence

The hierarchy for the *full* symmetric group is the sharpest instance: two `k`-tuples in
`X` lie in the same `Sym X`-orbit exactly when they have the same **kernel partition**
(`perm_orbit_iff_ker`). Hence, as soon as `k ≤ |X|`, the `k`-th level of the hierarchy
counts set partitions of a `k`-element set:
`#((X^k)/Sym X) = #(Setoid (Fin k))` (`orbits_perm_eq_card_setoid`).

Two consequences follow with no extra work:

* the **Poisson moment theorem** `∑_{σ ∈ Sym X} |fix σ|^k = P(k) · n!` for `k ≤ n`,
  where `P(k)` is the number of set partitions of a `k`-set (the `k`-th Bell number);
* the **log-convexity of the Bell sequence** `P(k+1)^2 ≤ P(k) · P(k+2)`, obtained by
  transporting the Cauchy–Schwarz inequality for fixed-point moments through the
  kernel classification. -/


variable {X : Type*} [Finite X] {k : ℕ}

theorem MomentHierarchy.orbits_perm_eq_card_setoid(hk : k ≤ Nat.card X) :
    Nat.card (orbitRel.Quotient (Equiv.Perm X) (Fin k → X)) = Nat.card (Setoid (Fin k)) := by sorry
