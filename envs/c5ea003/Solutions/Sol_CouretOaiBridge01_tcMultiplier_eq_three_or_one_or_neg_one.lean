-- Prove2me | solution 1 for CouretOaiBridge01.tcMultiplier_eq_three_or_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:02:35.949052+00:00
-- url     : https://prove2.me/submissions/591408d2-0814-4954-8489-3c912cd379b4

import Definitions.Def_Couret_BRIDGE01_B2_TCNonzeroChannels_1194a2978bc3
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
import Mathlib.Tactic

namespace CouretOaiBridge01

noncomputable section



private theorem char_u11_mul_self (χ : DirichletCharacter ℂ 30) :
    χ (u11 : ZMod 30) * χ (u11 : ZMod 30) = 1 := by
  calc
    χ (u11 : ZMod 30) * χ (u11 : ZMod 30)
        = χ ((u11 : ZMod 30) * (u11 : ZMod 30)) := by
            rw [map_mul]
    _ = χ ((u11 * u11 : U30) : ZMod 30) := by rfl
    _ = 1 := by rw [u11_sq]; simp

private theorem char_u29_mul_self (χ : DirichletCharacter ℂ 30) :
    χ (u29 : ZMod 30) * χ (u29 : ZMod 30) = 1 := by
  calc
    χ (u29 : ZMod 30) * χ (u29 : ZMod 30)
        = χ ((u29 : ZMod 30) * (u29 : ZMod 30)) := by
            rw [map_mul]
    _ = χ ((u29 * u29 : U30) : ZMod 30) := by rfl
    _ = 1 := by rw [u29_sq]; simp

theorem char_u11_eq_one_or_neg_one (χ : DirichletCharacter ℂ 30) :
    χ (u11 : ZMod 30) = 1 ∨ χ (u11 : ZMod 30) = -1 :=
  mul_self_eq_one_iff.mp (char_u11_mul_self χ)

theorem char_u29_eq_one_or_neg_one (χ : DirichletCharacter ℂ 30) :
    χ (u29 : ZMod 30) = 1 ∨ χ (u29 : ZMod 30) = -1 :=
  mul_self_eq_one_iff.mp (char_u29_mul_self χ)



theorem p2m_local_tcMultiplier_eq_three_or_one_or_neg_one (χ : DirichletCharacter ℂ 30) :
    tcMultiplier χ = 3 ∨ tcMultiplier χ = 1 ∨ tcMultiplier χ = -1 := by
  rcases char_u11_eq_one_or_neg_one χ with h11 | h11 <;>
    rcases char_u29_eq_one_or_neg_one χ with h29 | h29 <;>
    norm_num [tcMultiplier, h11, h29]

end

end CouretOaiBridge01

theorem solution : ∀
  (χ :
    @DirichletCharacter.{0} Complex
      (@CommGroupWithZero.toCommMonoidWithZero.{0} Complex
        (@Semifield.toCommGroupWithZero.{0} Complex (@Field.toSemifield.{0} Complex Complex.instField)))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))),
  Or
    (@Eq.{1} Complex (CouretOaiBridge01.tcMultiplier χ)
      (@OfNat.ofNat.{0} Complex (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 3) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
    (Or
      (@Eq.{1} Complex (CouretOaiBridge01.tcMultiplier χ)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
      (@Eq.{1} Complex (CouretOaiBridge01.tcMultiplier χ)
        (@Neg.neg.{0} Complex Complex.instNeg
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))) := @_root_.CouretOaiBridge01.p2m_local_tcMultiplier_eq_three_or_one_or_neg_one

