-- Prove2me | solution 1 for EnergyAscent.branch_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:20:55.745056+00:00
-- url     : https://prove2.me/submissions/0a53a048-2ac8-4fe1-a8e1-93339677f982

-- Sol generated from Combinatorics/EnergyAscentBerggrenLetters.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Theorems.Thm_parent_hyp_pos

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

/-- `a + 2b > 2c` is *exactly* the ratio condition `3a < 4b`. -/
theorem cond_left_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 2 * c < a + 2 * b ↔ 3 * a < 4 * b := by
  unfold IsPT at hpt
  constructor
  · intro h
    nlinarith [sq_nonneg (a + 2 * b - 2 * c)]
  · intro h
    nlinarith [sq_nonneg (a + 2 * b - 2 * c), sq_nonneg (a + 2 * b + 2 * c)]

/-- `2a + b > 2c` is *exactly* the ratio condition `3b < 4a`. -/
theorem cond_right_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 2 * c < 2 * a + b ↔ 3 * b < 4 * a := by
  unfold IsPT at hpt
  constructor
  · intro h
    nlinarith [sq_nonneg (2 * a + b - 2 * c)]
  · intro h
    nlinarith [sq_nonneg (2 * a + b - 2 * c), sq_nonneg (2 * a + b + 2 * c)]






/-! ## The branch letter -/






/-! ## Forward Barning–Hall generators -/










/-! ## The ratio band recovers the last generator -/




/-! ## Descent: the letter names the parent -/





open EnergyAscent in
theorem solution{a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) :
    (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ↔
      (3 * b < 4 * a ∧ 3 * a < 4 * b) := by
  have hL := cond_left_iff ha hb hc hpt
  have hR := cond_right_iff ha hb hc hpt
  have hpos := parent_hyp_pos a b c ha hb hc hpt
  constructor
  · rintro ⟨h1, h2, -⟩
    simp only [invB2] at h1 h2
    exact ⟨hR.mp (by omega), hL.mp (by omega)⟩
  · rintro ⟨h1, h2⟩
    have e1 := hL.mpr h2
    have e2 := hR.mpr h1
    refine ⟨by simp only [invB2]; omega, by simp only [invB2]; omega, ?_⟩
    simpa [invB2] using hpos
