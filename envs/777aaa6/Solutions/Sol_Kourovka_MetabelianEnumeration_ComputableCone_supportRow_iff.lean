-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.supportRow_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:53.461044+00:00
-- url     : https://prove2.me/submissions/b1641862-31a4-4338-8ce9-6c307ec92b38

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_supportRow_coeff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n r : ℕ) (v : VectorCode) (x : Fin n → ℝ) :
    (decodeRow n (supportRow r v)).eval x ≤ 0 ↔
      ConeVerifier.dot (decodeVector n v) x ≤ (1 / 2 : ℝ) ^ r := by
  have he : (decodeRow n (supportRow r v)).eval x =
      (2 ^ r : ℝ) * ConeVerifier.dot (decodeVector n v) x - 1 := by
    simp only [FourierMotzkin.Row.eval, supportRow_coeff, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    simp only [decodeRow, supportRow, Int.cast_neg, Int.cast_one]
    simp only [ConeVerifier.dot, Finset.mul_sum, mul_assoc]
    ring
  rw [he]
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  rw [one_div_pow]
  constructor
  · intro h
    apply (le_div_iff₀ hp).mpr
    nlinarith
  · intro h
    have h' := (le_div_iff₀ hp).mp h
    nlinarith
end Kourovka.MetabelianEnumeration.ComputableCone
