-- Prove2me | solution 1 for mme_CW_2376_modular_hash_XY_normal_forms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:36:59.362707+00:00
-- url     : https://prove2.me/submissions/b967097e-8f00-4d2a-995c-d5aded4859f7

import Definitions.Def_mme_CW_2376_modular_hash

open MME BigOperators

set_option autoImplicit false

/-- For an odd modulus the outer X and Y hashes have their expected affine
linear normal forms. -/
theorem solution
    {p N : ℕ} (hpodd : Odd p)
    (b0 : ZMod p) (w : Fin N → ZMod p)
    (x y : Fin N → Fin 5) :
    cw2376XHashMod w x =
        ∑ j, ((x j).val : ZMod p) * w j ∧
      cw2376YHashMod b0 w y =
        b0 + ∑ j, ((y j).val : ZMod p) * w j := by
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  constructor
  · simp only [cw2376XHashMod, cw2376DoubledXHash]
    rw [show (∑ j, ((2 * (x j).val : ℕ) : ZMod p) * w j) =
        2 * ∑ j, ((x j).val : ZMod p) * w j by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring]
    rw [← mul_assoc, htwo, one_mul]
  · simp only [cw2376YHashMod, cw2376DoubledYHash]
    rw [show (∑ j, ((2 * (y j).val : ℕ) : ZMod p) * w j) =
        2 * ∑ j, ((y j).val : ZMod p) * w j by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring]
    calc
      (2 : ZMod p)⁻¹ * (2 * b0 + 2 *
          ∑ j, ((y j).val : ZMod p) * w j) =
          ((2 : ZMod p)⁻¹ * 2) *
            (b0 + ∑ j, ((y j).val : ZMod p) * w j) := by ring
      _ = b0 + ∑ j, ((y j).val : ZMod p) * w j := by
        rw [htwo, one_mul]
