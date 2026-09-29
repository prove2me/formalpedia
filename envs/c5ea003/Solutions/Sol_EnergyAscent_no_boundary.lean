-- Prove2me | solution 1 for EnergyAscent.no_boundary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:23:41.081984+00:00
-- url     : https://prove2.me/submissions/e0ebb0a1-89ba-4d54-8181-cfd62a2be49b

-- Sol generated from Combinatorics/EnergyAscentBerggrenLetters.lean
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






/-! ## Forward Barning–Hall generators -/










/-! ## The ratio band recovers the last generator -/




/-! ## Descent: the letter names the parent -/





open EnergyAscent in
theorem solution{a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : 5 < c) (hprim : Int.gcd a b = 1) :
    4 * a ≠ 3 * b ∧ 4 * b ≠ 3 * a := by
  have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hprim
  constructor
  · intro h
    have hda : a ∣ 3 := hcop.dvd_of_dvd_mul_right ⟨4, by linarith⟩
    have hdb : b ∣ 4 := hcop.symm.dvd_of_dvd_mul_right ⟨3, by linarith⟩
    have ha3 : a ≤ 3 := Int.le_of_dvd (by norm_num) hda
    have hb4 : b ≤ 4 := Int.le_of_dvd (by norm_num) hdb
    unfold IsPT at hpt
    nlinarith
  · intro h
    have hdb : b ∣ 3 := hcop.symm.dvd_of_dvd_mul_right ⟨4, by linarith⟩
    have hda : a ∣ 4 := hcop.dvd_of_dvd_mul_right ⟨3, by linarith⟩
    have hb3 : b ≤ 3 := Int.le_of_dvd (by norm_num) hdb
    have ha4 : a ≤ 4 := Int.le_of_dvd (by norm_num) hda
    unfold IsPT at hpt
    nlinarith
