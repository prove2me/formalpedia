-- Prove2me | solution 1 for EnergyAscent.branchLetter_B2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:17:35.288335+00:00
-- url     : https://prove2.me/submissions/a8333d40-fdc6-419a-8987-dd28db6a305b

-- Sol generated from Combinatorics/EnergyAscentBerggrenLetters.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Theorems.Thm_EnergyAscent_branchLetter_eq_one_iff
import Theorems.Thm_EnergyAscent_leg_lt_hyp

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






/-! ## Forward Barning–Hall generators -/










/-! ## The ratio band recovers the last generator -/




/-! ## Descent: the letter names the parent -/





open EnergyAscent in
theorem solution{a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : branchLetter (B2 a b c).1 (B2 a b c).2.1 = 1 := by
  have h1 : a < c := leg_lt_hyp hb hc hpt
  have h2 : b < c := leg_lt_hyp ha hc (by unfold IsPT at *; linarith [hpt])
  rw [branchLetter_eq_one_iff]
  simp only [B2]
  omega
