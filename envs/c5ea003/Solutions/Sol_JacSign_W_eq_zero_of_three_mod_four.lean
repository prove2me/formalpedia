-- Prove2me | solution 1 for JacSign.W_eq_zero_of_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:07:35.810618+00:00
-- url     : https://prove2.me/submissions/588702c6-20dd-4439-b5cd-44b13dcaad68

-- Sol generated from Tropical/JacobiSignedWeilFloorCore.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_W_neg_reflect

/-!
# The Jacobi-signed circle count: core structure (JACSIGN)

For an odd prime `p` let `χ = quadraticChar (ZMod p)` be the Legendre character and let

`S(p) = {(x, y) ∈ (ZMod p)² : x² + y² = 1}`

be the unit circle over `ZMod p`.  The *Jacobi-signed circle count* is the character
weighted point count

`circleWeight p = ∑_{(x,y) ∈ S(p)} χ(x)`.

This file proves the basic structure of this weight:

* `JacSign.circleWeight_eq_W` : the geometric weight collapses to the **cubic character sum**
  `W p = ∑_x χ(x(1 - x²))`, i.e. the trace of Frobenius of the curve `y² = x - x³`
  (up to sign).
* `JacSign.W_neg_reflect` : the reflection identity `W p = χ(-1) · W p`.
* `JacSign.W_eq_zero_of_three_mod_four` : `W p = 0` whenever `p ≡ 3 (mod 4)` — the
  supersingular half of the primes carries **no** signal at all.
* `JacSign.W_even` : `W p` is always even, so the weight can never be an odd number;
  this matches the observed data `-2, -10, 6, -18, 14, 22`.

These are the structural facts underlying the JACSIGN experiment; the Weil bound
`W p ^ 2 ≤ 4 p` is proved in `JacobiSignedWeilFloorBound.lean`.
-/

open Finset

open JacSign



variable (p : ℕ) [Fact p.Prime]



theorem chi_neg_one_eq_neg_one (hp : p % 4 = 3) : quadraticChar (ZMod p) (-1) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_neg_one_iff]
  simp [hp]








open JacSign in
theorem solution(hp : p % 4 = 3) : W p = 0 := by
  have h := W_neg_reflect p
  rw [chi_neg_one_eq_neg_one p hp] at h
  linarith
