-- Prove2me | Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
-- name    : Combinatorics_EnergyAscentBerggrenLetters
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:38:59.438163+00:00
-- url     : https://prove2.me/theorems/dd9d30a6-677a-44cd-b054-4745af427758
-- title:
--   Aether Catalog definitions — Combinatorics_EnergyAscentBerggrenLetters
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EnergyAscentBerggrenLetters`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EnergyAscentBerggrenLetters.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt

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

namespace EnergyAscent

open scoped Classical

/-! ## Elementary Pythagorean estimates -/



/-! ## The three branch conditions are ratio bands -/








/-! ## The branch letter -/

/-- The **branch letter** of a triple, read off from the leg ratio alone:
`0` when `a/b < 3/4`, `2` when `a/b > 4/3`, and `1` in the middle band.
This is a purely positional (magnitude) statistic — no residue information is
used. -/
def branchLetter (a b : ℤ) : Fin 3 :=
  if 4 * a < 3 * b then 0 else if 4 * b < 3 * a then 2 else 1





/-! ## Forward Barning–Hall generators -/

/-- First forward Barning–Hall generator. -/
def B1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a - 2 * b + 2 * c, 2 * a - b + 2 * c, 2 * a - 2 * b + 3 * c)

/-- Second forward Barning–Hall generator. -/
def B2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b + 2 * c, 2 * a + b + 2 * c, 2 * a + 2 * b + 3 * c)

/-- Third forward Barning–Hall generator. -/
def B3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a + 2 * b + 2 * c, -2 * a + b + 2 * c, -2 * a + 2 * b + 3 * c)







/-! ## The ratio band recovers the last generator -/




/-! ## Descent: the letter names the parent -/




end EnergyAscent


