-- Prove2me | solution 1 for Moebius.ZM.tw_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:41:50.84408+00:00
-- url     : https://prove2.me/submissions/dbdcb9fc-1b9d-49df-9541-be33591a39a8

/-
# `Moebius.ZM.tw_pow_eq_one_iff`
Target `e91a5dde` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`ZM` is the subring `{(u,v) ∈ ℤ × ℤ | u ≡ v mod 2}`, realising `ℤ[t]/(t²−1)` via
`a + b·t ↦ (a+b, a−b)`. So `tw = mk 0 1 = (1, −1)` and `1 = (1, 1)`, and since a subring inherits
arithmetic componentwise, `tw ^ n = (1, (−1)^n)`. The first components agree for EVERY n, so the
whole statement rests on the second: `(−1)^n = 1 ↔ Even n`.

Verified in character coordinates for n = 0..12, both sides agreeing. Two edges checked on purpose:
n = 0 (empty product is 1, and 0 is Even — consistent, and the case such proofs usually break on),
and closure — across 200 exponents the coordinate difference stayed even, as a subring requires.

The bundle retains NO theorems. Its header advertises `tw_sq`, `isUnit_tw`, `nrm_mul` and more;
skeleton subtraction stripped all of them, so the order-two fact CANNOT be cited and is derived
here from the definition plus componentwise arithmetic.

PROBED, NOT GUESSED — all `#check`ed, and both probe examples compiled silently:
  * `neg_one_pow_eq_one_iff_even : -1 ≠ 1 → ((-1)^n = 1 ↔ Even n)`  (note the side condition)
  * `SetLike.coe_eq_coe : ↑x = ↑y ↔ x = y`
  * `Subring.coe_pow : ↑(x ^ n) = ↑x ^ n`,  `Subring.coe_one : ↑1 = 1`
  * `((tw : ZM) : ℤ × ℤ) = (1, -1)` by `simp [tw, mk]`
  * traced goal after `rw [← SetLike.coe_eq_coe]` is `↑(tw ^ n) = ↑1 ↔ Even n`
-/
import Mathlib
import Definitions.Def_MachineLearning_MoebiusTwistRing

set_option autoImplicit false
set_option maxHeartbeats 400000

open Moebius Moebius.ZM in
/-- **The target, verbatim.** -/
theorem solution (n : ℕ) : tw ^ n = 1 ↔ Even n := by
  have htw : ((tw : ZM) : ℤ × ℤ) = (1, -1) := by simp [tw, mk]
  rw [← SetLike.coe_eq_coe, Subring.coe_pow, Subring.coe_one, htw, Prod.ext_iff]
  -- first components are 1 ^ n = 1 and hold always; the content is the second
  simp
  exact neg_one_pow_eq_one_iff_even (by decide)
