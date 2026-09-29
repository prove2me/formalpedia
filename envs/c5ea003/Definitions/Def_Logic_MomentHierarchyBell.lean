-- Prove2me | Definitions.Def_Logic_MomentHierarchyBell
-- name    : Logic_MomentHierarchyBell
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:57:17.797356+00:00
-- url     : https://prove2.me/theorems/3a2d8baf-2f16-40f2-ac2d-7932861d8536
-- title:
--   Aether Catalog definitions — Logic_MomentHierarchyBell
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.MomentHierarchyBell`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/MomentHierarchyBell.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

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

namespace MomentHierarchy

/-! ## Cycle 4: instantiation at the symmetric group

For the natural action of `Equiv.Perm X` on a finite `X` the hierarchy becomes the
moment sequence of the number of fixed points of a uniformly random permutation. The
action is transitive and 2-transitive, so the first two moments are `1` and `2` — the
first two Bell numbers, i.e. the first two moments of a Poisson(1) variable. -/

section Symmetric

variable (X : Type*) [Fintype X] [DecidableEq X]





end Symmetric


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

section Kernels

variable {X : Type*} [Finite X] {k : ℕ}




end Kernels

section Bell

/-- `partitionCount k` is the number of set partitions of a `k`-element set, i.e. the
`k`-th Bell number, realised as the number of equivalence relations on `Fin k`. -/
noncomputable def partitionCount (k : ℕ) : ℕ := Nat.card (Setoid (Fin k))













end Bell


/-! ## Lab notes: measured data behind the theorems

Exhaustive enumeration (outside Lean) of `S_k := ∑_{g ∈ G} |X^g|^k` and
`o_k := #((X^k)/G)` for several actions; every row satisfies `S_k = o_k · |G|`
(`sum_fixedPoints_pow_eq_orbits_mul_card`) and `o_{k+1}^2 ≤ o_k · o_{k+2}`
(`orbitCount_log_convex`):

| action                 | `|G|` | `o_0 … o_5`            |
|------------------------|-------|------------------------|
| `S_3` on `3` points    | `6`   | `1, 1, 2, 5, 14, 41`   |
| `S_4` on `4` points    | `24`  | `1, 1, 2, 5, 15, 51`   |
| `A_4` on `4` points    | `12`  | `1, 1, 2, 6, 22, 86`   |
| `D_4` on `4` points    | `8`   | `1, 1, 3, 10, 36, 136` |
| `C_4` regular          | `4`   | `1, 1, 4, 16, 64, 256` |
| trivial group, `3` pts | `1`   | `1, 3, 9, 27, 81, 243` |

The symmetric-group rows are Bell numbers truncated to at most `n` blocks
(`o_k = P(k)` exactly while `k ≤ n`, cf. `orbitCount_perm_eq_partitionCount`:
`S_4` gives `51 = 52 - 1` at `k = 5` because partitions into `5` blocks are not
realisable on `4` points). The `C_4` row is `|G|^{k-1}` (`orbitCount_regular_eq`).
The two machine-checked numerical instances below reproduce entries of this table. -/

section LabNotes



end LabNotes

end MomentHierarchy


