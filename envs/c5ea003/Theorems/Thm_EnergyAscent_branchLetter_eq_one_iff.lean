-- Prove2me | Theorems.Thm_EnergyAscent_branchLetter_eq_one_iff
-- name    : EnergyAscent.branchLetter_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:14:38.144919+00:00
-- url     : https://prove2.me/theorems/8c968121-d8df-4460-b96c-a5258c94d28c
-- title:
--   BranchLetter eq one iff
-- statement:
--   Formal statement of `EnergyAscent.branchLetter_eq_one_iff` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem EnergyAscent.branchLetter_eq_one_iff(a b : ℤ) :
--       branchLetter a b = 1 ↔ (3 * b ≤ 4 * a ∧ 3 * a ≤ 4 * b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentBerggrenLetters.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentBerggrenLetters.lean#L175

-- Thm stub generated from Combinatorics/EnergyAscentBerggrenLetters.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters

/-!
# Energy-Ascent I: the Berggren branch letter is exactly a ratio band

This file formalises the *control* experiment of the ENERGY-ASCENT round
(`ratio-band → b₁ exact 3000/3000`): the first Berggren / Barning–Hall branch
letter of a primitive Pythagorean triple is a **deterministic function of the
leg ratio `a / b` alone** — a purely positional (order-theoretic, magnitude)
quantity — and conversely the leg ratio band recovers the last generator used
to produce the triple.

We build directly on the catalog module
`Combinatorics.BerggrenTrees.Parent_hyp_lt`, reusing `IsPT`, `invB1`, `invB2`,
`invB3`, `parent_hyp_pos`, `parent_hyp_lt`.

## Main results

* `EnergyAscent.branch_one_iff`, `branch_two_iff`, `branch_three_iff`:
  positivity of the three inverse Barning–Hall parents is *equivalent* to an
  explicit band for the leg ratio, namely `4a < 3b`, `3b < 4a ∧ 3a < 4b`,
  `4b < 3a`.
* `EnergyAscent.branchLetter_eq_descent`: the band-defined letter agrees with
  the descent branch for every non-root primitive triple.
* `EnergyAscent.branchLetter_B1/B2/B3`: applying the `i`-th forward generator
  produces a triple whose ratio band is exactly `i` — the ratio band recovers
  the last letter, for *all* triples (not merely on a sample of 3000).
* `EnergyAscent.branchLetter_ratio_invariant`: the letter is a function of the
  ratio: two triples with `a * b' = a' * b` have the same letter.  This is the
  formal content of "the mechanism is positional".
-/

open EnergyAscent

open scoped Classical

/-! ## Elementary Pythagorean estimates -/



/-! ## The three branch conditions are ratio bands -/








/-! ## The branch letter -/

theorem EnergyAscent.branchLetter_eq_one_iff(a b : ℤ) :
    branchLetter a b = 1 ↔ (3 * b ≤ 4 * a ∧ 3 * a ≤ 4 * b) := by sorry
