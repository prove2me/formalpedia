-- Prove2me | solution 1 for JacSign.circleWeight_eq_W
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:15:12.18398+00:00
-- url     : https://prove2.me/submissions/b1e8388b-e9e1-415b-93d7-4f2e54fa5ce0

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
theorem solution(hp : p ≠ 2) : circleWeight p = W p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have key : ∀ a : ZMod p,
      ((univ.filter (fun y : ZMod p => y ^ 2 = a)).card : ℤ) = quadraticChar (ZMod p) a + 1 := by
    intro a
    simpa [Set.toFinset_setOf] using quadraticChar_card_sqrts (F := ZMod p) hF a
  have step : ∀ x : ZMod p,
      (∑ y : ZMod p, if x ^ 2 + y ^ 2 = 1 then quadraticChar (ZMod p) x else 0)
        = quadraticChar (ZMod p) x * (quadraticChar (ZMod p) (1 - x ^ 2) + 1) := by
    intro x
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have hset : (univ.filter (fun y : ZMod p => x ^ 2 + y ^ 2 = 1))
        = (univ.filter (fun y : ZMod p => y ^ 2 = 1 - x ^ 2)) := by
      apply Finset.filter_congr
      intro y _
      constructor <;> intro h <;> linear_combination h
    rw [hset, nsmul_eq_mul, smul_zero, add_zero, ← key (1 - x ^ 2), mul_comm]
  simp only [circleWeight, step, mul_add, mul_one, Finset.sum_add_distrib]
  rw [quadraticChar_sum_zero hF, add_zero]
  simp [W, map_mul]
