-- Prove2me | Theorems.Thm_TraceDistribution_fixedCard_regular
-- name    : TraceDistribution.fixedCard_regular
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:57:08.070641+00:00
-- url     : https://prove2.me/theorems/5ef8d3b4-aad1-44d1-8f21-584ad1e4b1d3
-- title:
--   The regular action is free: only the identity fixes anything.
-- statement:
--   The regular action is free: only the identity fixes anything.
--
--   ```lean
--   theorem TraceDistribution.fixedCard_regular[DecidableEq G] (g : G) :
--       fixedCard G g = if g = 1 then Nat.card G else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TraceDistribution/Examples.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TraceDistribution/Examples.lean#L45

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

omit [Fintype G] in

theorem TraceDistribution.fixedCard_regular[DecidableEq G] (g : G) :
    fixedCard G g = if g = 1 then Nat.card G else 0 := by sorry
