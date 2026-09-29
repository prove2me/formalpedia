-- Prove2me | solution 1 for JacSign.W_neg_reflect
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:05:53.284798+00:00
-- url     : https://prove2.me/submissions/c36f68d7-bfdd-4bc0-b7d5-9712522a4529

-- Sol generated from Tropical/JacobiSignedWeilFloorCore.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

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
theorem solution: W p = quadraticChar (ZMod p) (-1) * W p := by
  have hrefl : ∀ x : ZMod p, quadraticChar (ZMod p) (x * (1 - x ^ 2))
      = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) ((-x) * (1 - (-x) ^ 2)) := by
    intro x
    rw [← map_mul]
    congr 1
    ring
  calc W p = ∑ x : ZMod p, quadraticChar (ZMod p) (-1) *
              quadraticChar (ZMod p) ((-x) * (1 - (-x) ^ 2)) := by
        rw [W]; exact Finset.sum_congr rfl fun x _ => hrefl x
    _ = quadraticChar (ZMod p) (-1) * W p := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => rfl
