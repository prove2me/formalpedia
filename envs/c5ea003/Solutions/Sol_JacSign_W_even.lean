-- Prove2me | solution 1 for JacSign.W_even
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:13:26.035136+00:00
-- url     : https://prove2.me/submissions/c4540a5c-a44a-4c5f-be9a-99ccab73cce3

-- Sol generated from Tropical/JacobiSignedWeilFloorCore.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_W_eq_zero_of_three_mod_four
import Theorems.Thm_JacSign_chi_neg_one_eq_one
import Theorems.Thm_JacSign_sum_even_of_neg_invariant

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
theorem solution(hp : p ≠ 2) : (2 : ℤ) ∣ W p := by
  have hprime := (Fact.out : p.Prime)
  have hodd : p % 2 = 1 := hprime.eq_two_or_odd.resolve_left hp
  by_cases h4 : p % 4 = 3
  · rw [W_eq_zero_of_three_mod_four p h4]; exact dvd_zero 2
  have h1 : p % 4 = 1 := by
    have := hprime.two_le
    omega
  refine sum_even_of_neg_invariant p hp (fun x => quadraticChar (ZMod p) (x * (1 - x ^ 2)))
    (fun x => ?_) (by simp)
  show quadraticChar (ZMod p) ((-x) * (1 - (-x) ^ 2)) = quadraticChar (ZMod p) (x * (1 - x ^ 2))
  have hx : quadraticChar (ZMod p) ((-x) * (1 - (-x) ^ 2))
      = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (x * (1 - x ^ 2)) := by
    rw [← map_mul]; congr 1; ring
  rw [hx, chi_neg_one_eq_one p h1, one_mul]
