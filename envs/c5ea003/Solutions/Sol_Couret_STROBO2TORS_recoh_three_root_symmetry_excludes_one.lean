-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_three_root_symmetry_excludes_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:39.327959+00:00
-- url     : https://prove2.me/submissions/d2ccc66a-4476-4228-9fd7-ff1aceafc0d7

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
An elementary algebraic gate for the nonvanishing of three 2-primary
complex roots. This file does NOT yet prove the full nonvanishing
theorem or construct the RECOH character bank.
-/

namespace Couret.STROBO2TORS





/-- In a domain, the normalized equation 1 + b + c = 0 with
bc + b + c = 0 cannot hold with b = 1. -/
theorem p2m_local_recoh_three_root_symmetry_excludes_one
    (b c : ℂ)
    (hsum : 1 + b + c = 0)
    (hpair : b + c + b * c = 0) :
    b ≠ 1 := by
  intro hb
  rw [hb] at hsum hpair
  have hc : c = -2 := by
    linear_combination hsum
  rw [hc] at hpair
  norm_num at hpair

end Couret.STROBO2TORS


theorem solution : ∀ (b c : Complex),
  @Eq.{1} Complex
      (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) b)
        c)
      (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →
    @Eq.{1} Complex
        (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) b c)
          (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) b c))
        (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →
      @Ne.{1} Complex b (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_three_root_symmetry_excludes_one

