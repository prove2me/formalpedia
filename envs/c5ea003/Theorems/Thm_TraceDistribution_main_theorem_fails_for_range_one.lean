-- Prove2me | Theorems.Thm_TraceDistribution_main_theorem_fails_for_range_one
-- name    : TraceDistribution.main_theorem_fails_for_range_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:57:27.000988+00:00
-- url     : https://prove2.me/theorems/2fc40122-8a08-4e2b-af59-248a3c3418b3
-- title:
--   The range in the main theorem cannot be shortened to `k ≤ 1`.
-- statement:
--   **The range in the main theorem cannot be shortened to `k ≤ 1`.**  Stated as the
--   falsity of the would-be strengthening, over all finite groups and all finite `G`-sets.
--
--   ```lean
--   theorem TraceDistribution.main_theorem_fails_for_range_one:
--       ¬ (∀ (G : Type) [Group G] [Fintype G] (X Y : Type)
--           [MulAction G X] [MulAction G Y] [Finite X] [Finite Y],
--           (∀ k ≤ 1, orbitCount G X k = orbitCount G Y k) →
--             traceDistribution G X = traceDistribution G Y) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TraceDistribution/Examples.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TraceDistribution/Examples.lean#L144

-- Thm stub generated from Logic/TraceDistribution/Examples.lean
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core
/-
# The threshold in Conjecture A is not an artefact: low-degree data is genuinely blind

`Logic.TraceDistribution.Core` proves that the trace distribution of a finite
`G`-action is determined by the orbit counts on `k`-tuples for `k ≤ max |X| |Y|`.
It is natural to ask whether the plain orbit count (`k = 1`, i.e. Burnside's lemma
itself) already suffices.  It does not, and the failure is universal:

For **every** finite group `G` with `|G| ≥ 2`, the *regular* `G`-set `G` and the
*one-point* `G`-set `Unit` have

* the same number of orbits on `0`-tuples (both `1`),
* the same number of orbits on `1`-tuples (both `1`),
* but different numbers of orbits on `2`-tuples (`|G|` versus `1`),

and consequently different trace distributions (`{|G|, 0, …, 0}` versus
`{1, 1, …, 1}`).  See `regular_ne_point`.

Taking `G` of order `2` makes this optimal on the nose: there `max |X| |Y| = 2`, so
the range `k ≤ 2` supplied by the main theorem is exactly the range needed.

## Lab notes (experimental data)

`G = ℤ/2`:

| action        | trace distribution | `k=0` | `k=1` | `k=2` | `k=3` |
|---------------|--------------------|-------|-------|-------|-------|
| regular `G`   | `{2, 0}`           | 1     | 1     | 2     | 4     |
| point `Unit` | `{1, 1}`           | 1     | 1     | 1     | 1     |

`G = ℤ/3`: regular `{3,0,0}` gives `1, 1, 3, 9, …`; point `{1,1,1}` gives `1, 1, 1, …`.
In general `|orbits on G^k| = |G|^{k-1}` for the regular action and `1` for the point.
-/

open MulAction Finset

open TraceDistribution

variable {G : Type*} [Group G] [Fintype G]

/-! ## Fixed-point counts of the two extreme `G`-sets -/



/-! ## Power sums of the two extreme `G`-sets -/



/-! ## Orbit counts of the two extreme `G`-sets -/




/-! ## The separation -/

theorem TraceDistribution.main_theorem_fails_for_range_one:
    ¬ (∀ (G : Type) [Group G] [Fintype G] (X Y : Type)
        [MulAction G X] [MulAction G Y] [Finite X] [Finite Y],
        (∀ k ≤ 1, orbitCount G X k = orbitCount G Y k) →
          traceDistribution G X = traceDistribution G Y) := by sorry
