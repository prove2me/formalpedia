-- Prove2me | solution 1 for mme_CW_2376_modular_hash_AP_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:05:14.250861+00:00
-- url     : https://prove2.me/submissions/194a4f81-2352-4053-a03d-618e7879b6c0

import Definitions.Def_mme_CW_2376_modular_hash
import Theorems.Thm_mme_CW_2376_doubled_hash_AP_identity

open MME

set_option autoImplicit false

theorem solution
    {M m : ℕ} (hM : Odd M)
    (b0 : ZMod M) (w : Fin (cw2376ProfileLength m) → ZMod M)
    (x y z : CW2376ProfileAddress m)
    (hsupp : CW2376CoordinatewiseSupported
      (cw2376MixedAddress x y z)) :
    cw2376XHashMod w (x 0) + cw2376YHashMod b0 w (y 1) =
      2 * cw2376ZHashMod b0 w (z 2) := by
  have hunit : IsUnit (2 : ZMod M) :=
    (ZMod.isUnit_iff_coprime 2 M).2 hM.coprime_two_left
  have hAP := mme_CW_2376_doubled_hash_AP_identity b0 w x y z hsupp
  simp only [cw2376XHashMod, cw2376YHashMod, cw2376ZHashMod]
  calc
    (2 : ZMod M)⁻¹ * cw2376DoubledXHash w (x 0) +
          (2 : ZMod M)⁻¹ * cw2376DoubledYHash b0 w (y 1) =
        (2 : ZMod M)⁻¹ *
          (cw2376DoubledXHash w (x 0) +
            cw2376DoubledYHash b0 w (y 1)) := by ring
    _ = (2 : ZMod M)⁻¹ *
        (2 * cw2376DoubledZHash b0 w (z 2)) := by rw [hAP]
    _ = cw2376DoubledZHash b0 w (z 2) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit (2 : ZMod M) hunit, one_mul]
    _ = 2 * ((2 : ZMod M)⁻¹ *
        cw2376DoubledZHash b0 w (z 2)) := by
      rw [← mul_assoc, ZMod.mul_inv_of_unit (2 : ZMod M) hunit, one_mul]
