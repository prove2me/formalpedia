-- Prove2me | solution 1 for mme_CW_q6_hash_bucket_coherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:57:53.392896+00:00
-- url     : https://prove2.me/submissions/9e17ab71-7ca8-41ad-bb3a-2e259aa47cdc

import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME

/-- Retained lower-half Salem--Spencer labels of a supported mixed address
must agree.  Doubling is cancellable because the CW modulus is odd. -/
theorem solution
    (N Xcount : ℕ)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1))
    (x y z : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x y z))
    (sx sy sz : ℕ) (hsx : sx ∈ S) (hsy : sy ∈ S) (hsz : sz ∈ S)
    (hx : cwQ6DoubledXHash b0 w (x 0) =
      2 * (sx : ZMod (4 * Xcount ^ 2 + 1)))
    (hy : cwQ6DoubledYHash b0 w (y 1) =
      2 * (sy : ZMod (4 * Xcount ^ 2 + 1)))
    (hz : cwQ6DoubledZHash b0 w (z 2) =
      2 * (sz : ZMod (4 * Xcount ^ 2 + 1))) :
    sx = sy ∧ sy = sz := by
  let Mmod : ℕ := 4 * Xcount ^ 2 + 1
  have hhash := mme_CW_q6_doubled_hash_AP_identity b0 w x y z hsupp
  rw [hx, hy, hz] at hhash
  have hodd : Odd Mmod := by
    refine ⟨2 * Xcount ^ 2, ?_⟩
    dsimp [Mmod]
    omega
  have htwoUnit : IsUnit (2 : ZMod Mmod) := by
    change IsUnit ((2 : ℕ) : ZMod Mmod)
    rw [ZMod.isUnit_iff_coprime]
    exact hodd.coprime_two_left
  have hmod : (sx : ZMod Mmod) + (sy : ZMod Mmod) =
      2 * (sz : ZMod Mmod) := by
    apply htwoUnit.mul_left_cancel
    simpa [mul_add, mul_assoc] using hhash
  have hcollision := mme_threeAP_free_half_modulus_no_collision
    Mmod S (by simpa [Mmod] using hSrange) hSfree sx sz sy hsx hsz hsy hmod
  exact ⟨hcollision.1.trans hcollision.2, hcollision.2.symm⟩
