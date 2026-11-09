-- Prove2me | solution 1 for Couret.canonical_mask_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:36.306715+00:00
-- url     : https://prove2.me/submissions/2f993330-ed90-4a94-a469-cf57f5651785

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret















theorem bitIndex_codeOfBit : ∀ i : Fin 8, bitIndex30 (codeOfBit i) = i.val := by decide















theorem p2m_local_canonical_mask_injective (a b : Nat) (ha : a < 256) (hb : b < 256)
    (he : ∀ u : Code30, maskSupport a u ↔ maskSupport b u) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have h := he (codeOfBit ⟨i,hi⟩)
    change (a.testBit (bitIndex30 (codeOfBit ⟨i,hi⟩)) = true ↔
      b.testBit (bitIndex30 (codeOfBit ⟨i,hi⟩)) = true) at h
    rw [bitIndex_codeOfBit] at h
    cases h₁ : a.testBit i <;> cases h₂ : b.testBit i <;> simp_all
  · have hma : a % 2^8 = a := Nat.mod_eq_of_lt ha
    have hmb : b % 2^8 = b := Nat.mod_eq_of_lt hb
    have h₁ := Nat.testBit_mod_two_pow a 8 i
    have h₂ := Nat.testBit_mod_two_pow b 8 i
    rw [hma] at h₁
    rw [hmb] at h₂
    simp only [hi, decide_false, Bool.false_and] at h₁ h₂
    exact h₁.trans h₂.symm



















































end Couret


theorem solution : ∀ (a b : Nat),
  @LT.lt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) →
    @LT.lt.{0} Nat instLTNat b (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) →
      (∀ (u : Couret.Code30), Iff (Couret.maskSupport a u) (Couret.maskSupport b u)) → @Eq.{1} Nat a b := @_root_.Couret.p2m_local_canonical_mask_injective

