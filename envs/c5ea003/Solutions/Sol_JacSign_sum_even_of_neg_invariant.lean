-- Prove2me | solution 1 for JacSign.sum_even_of_neg_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:11:46.660089+00:00
-- url     : https://prove2.me/submissions/ac530c88-505f-4540-a56e-479b11bf0123

-- Sol generated from Tropical/JacobiSignedWeilFloorCore.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_sum_eq_two_mul_half

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











open JacSign in
theorem solution(hp : p ≠ 2) (f : ZMod p → ℤ)
    (hfneg : ∀ x : ZMod p, f (-x) = f x) (hf0 : f 0 = 0) :
    (2 : ℤ) ∣ ∑ x : ZMod p, f x :=
  ⟨_, sum_eq_two_mul_half p hp f hfneg hf0⟩
