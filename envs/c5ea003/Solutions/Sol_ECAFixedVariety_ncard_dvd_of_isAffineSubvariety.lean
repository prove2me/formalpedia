-- Prove2me | solution 1 for ECAFixedVariety.ncard_dvd_of_isAffineSubvariety
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:05:30.689337+00:00
-- url     : https://prove2.me/submissions/d74c9082-5852-48df-8a1a-e3f48b68f5e2

-- Sol generated from Novelty/ECAFixedVarietyNoDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyNoDimension
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree

/-!
# When the fixed-point "variety" has no dimension at all

The conjecture under test presupposes that `V(f) = {s : f(s) = s}` is a linear
(or at least affine) subvariety of `𝔸ⁿ_{𝔽₂}`, so that `dim V(f)` makes sense.
This file shows that the presupposition fails for *most* elementary cellular
automata, by two independent obstructions.

**Obstruction 1 (parity / origin).**  `V(f)` contains the origin iff the local
rule sends the zero neighbourhood to `0`, i.e. iff the Wolfram number is even.
Hence for all `128` odd rules the fixed locus is not a linear subspace, whatever
`n` is (`odd_rule_no_fixed_dim`).

**Obstruction 2 (Lagrange).**  An affine subvariety of `𝔸ⁿ_{𝔽₂}` has cardinality
dividing `2ⁿ` (`ncard_dvd_of_isAffineSubvariety`).  The majority Rule 232 has
exactly `6` stationary configurations on the ring of size `4`, and `6 ∤ 16`;
Rule 45 has exactly `3` on the ring of size `3`, and `3 ∤ 8`.  So these loci are
not even affine subvarieties (`rule232_not_affine`, `rule45_not_affine`).

Finally `wolfram_fixedpoint_dimension_conjecture_false` collects the falsifying
evidence: the class-4 Rule 110 has the *minimal* variety, the class-3 Rule 90
has dimension `≤ 2` no matter how large `n` is, the class-3 Rule 45 has an empty
variety for `3 ∤ n`, and the class-2 Rule 232 has no dimension at all.
-/

open ECAFixedVariety


/-! ### Obstruction 1: odd rules miss the origin -/





/-! ### Obstruction 2: a Lagrange bound on affine subvarieties -/





/-! ### The majority Rule 232 -/





/-! ### Rule 45 again: not even affine -/



/-! ### Synthesis -/



open ECAFixedVariety in
theorem solution{n : ℕ} [NeZero n] {S : Set (Cfg n)}
    (h : IsAffineSubvariety S) : S.ncard ∣ 2 ^ n := by
  obtain ⟨v, W, rfl⟩ := h
  have hinj : Function.Injective (fun w : Cfg n => v + w) := add_right_injective v
  rw [Set.ncard_image_of_injective _ hinj]
  have hcard : (W : Set (Cfg n)).ncard = Nat.card W := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  have hdvd : Nat.card W.toAddSubgroup ∣ Nat.card (Cfg n) :=
    AddSubgroup.card_addSubgroup_dvd_card W.toAddSubgroup
  have hamb : Nat.card (Cfg n) = 2 ^ n := by
    simp [Cfg, Nat.card_eq_fintype_card]
  rw [hamb] at hdvd
  exact hdvd
