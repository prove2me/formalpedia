-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_complex_character_bank_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:21.851148+00:00
-- url     : https://prove2.me/submissions/1eb0e5d8-9ebc-4fbc-9978-aa2332d0e611

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_binary_encoding
import Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_zmod_encoding
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_bank_collision_of_binary_card
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Choose

set_option autoImplicit false

/-!
RECOH: character restrictions provide their own finite-field encodings.

Every complex additive character on a group annihilated by n factors
through the standard character of ZMod n. The binary and ternary
specializations discharge the compatibility assumptions of the existing
short-bank collision theorem. No primary character extension or upper
bound is assumed here.
-/

namespace Couret.STROBO2TORS







/-- An actual complex character restricted to exponent three has an
additive ternary encoding with precisely the same kernel. -/
theorem recoh_complex_character_ternary_encoding
    {V : Type*} [AddCommGroup V]
    (h3 : ∀ a : V, (a + a) + a = 0) (chi : AddChar V ℂ) :
    ∃ bits : V →+ ZMod 3, ∀ a : V, bits a = 0 ↔ chi a = 1 := by
  have hexp : ∀ a : V, (3 : ℕ) • a = 0 := by
    intro a
    change (2 + 1 : ℕ) • a = 0
    simpa only [add_nsmul, two_nsmul, one_nsmul] using h3 a
  obtain ⟨bits, hbits⟩ := recoh_complex_character_zmod_encoding 3 hexp chi
  refine ⟨bits, ?_⟩
  intro a
  rw [← hbits a, ← (ZMod.stdAddChar (N := 3)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every short bank of genuine complex characters has a collision.
Binary/ternary encodings and their compatibility are constructed internally;
only the torsion structure, embeddings and a triple witness remain explicit. -/
theorem p2m_local_recoh_short_complex_character_bank_collision
    {H V : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (hcardH : Fintype.card H = 2 ^ r)
    (h2 : ∀ a : H, a + a = 0)
    (h3 : ∀ a : V, (a + a) + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (embV : V →+ G) (injV : Function.Injective embV)
    (bank : Fin k → AddChar G ℂ)
    (x y z : G) (hcard : ({x, y, z} : Finset G).card = 3) :
    (∃ d : G, d ≠ 0 ∧ d + d = 0 ∧
      ({x, y, z} : Finset G) ≠ {x + d, y + d, z + d} ∧
      (∀ q : G,
        orderedSquare ({x, y, z} : Finset G) q =
          orderedSquare ({x + d, y + d, z + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) x y z =
          recohTripleProbe (bank i) (x + d) (y + d) (z + d))) ∨
    (∃ d v : G, d ≠ 0 ∧ d + d = 0 ∧
      v ≠ 0 ∧ (v + v) + v = 0 ∧
      ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} ∧
      (∀ q : G,
        orderedSquare ({0, v, v + d} : Finset G) q =
          orderedSquare ({0, -v, -v + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) 0 v (v + d) =
          recohTripleProbe (bank i) 0 (-v) (-v + d))) := by
  classical
  have hb := fun i : Fin k =>
    recoh_complex_character_binary_encoding h2
      ((bank i).compAddMonoidHom embH)
  choose binary hbinary hnegative using hb
  have ht := fun i : Fin k =>
    recoh_complex_character_ternary_encoding h3
      ((bank i).compAddMonoidHom embV)
  choose ternary hternary using ht
  exact recoh_short_bank_collision_of_binary_card r s k hr hk hcardV hcardH
    h2 h3 embH injH embV injV (fun i => (bank i : G → ℂ))
    (fun i => (bank i).map_add_eq_mul) (fun i => (bank i).map_zero_eq_one)
    binary (fun i a ha => (hbinary i a).mp ha) hnegative
    ternary (fun i a ha => (hternary i a).mp ha) x y z hcard

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {H : Type p2m_u_1}
  {V : Type p2m_u_2} [inst_2 : AddCommGroup.{p2m_u_1} H] [inst_3 : Fintype.{p2m_u_1} H]
  [inst_4 : AddCommGroup.{p2m_u_2} V] [inst_5 : Fintype.{p2m_u_2} V] (r s k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat k (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r s) →
      @Eq.{1} Nat (@Fintype.card.{p2m_u_2} V inst_5)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
        @Eq.{1} Nat (@Fintype.card.{p2m_u_1} H inst_3)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
          (∀ (a : H),
              @Eq.{p2m_u_1 + 1} H
                (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} H H H
                  (@instHAdd.{p2m_u_1} H
                    (@AddCommMagma.toAdd.{p2m_u_1} H
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} H
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} H
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} H inst_2)))))
                  a a)
                (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_1} H
                    (@NegZeroClass.toZero.{p2m_u_1} H
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_2)))))))) →
            (∀ (a : V),
                @Eq.{p2m_u_2 + 1} V
                  (@HAdd.hAdd.{p2m_u_2, p2m_u_2, p2m_u_2} V V V
                    (@instHAdd.{p2m_u_2} V
                      (@AddCommMagma.toAdd.{p2m_u_2} V
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_2} V
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_2} V
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_2} V inst_4)))))
                    (@HAdd.hAdd.{p2m_u_2, p2m_u_2, p2m_u_2} V V V
                      (@instHAdd.{p2m_u_2} V
                        (@AddCommMagma.toAdd.{p2m_u_2} V
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_2} V
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_2} V
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_2} V inst_4)))))
                      a a)
                    a)
                  (@OfNat.ofNat.{p2m_u_2} V (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_2} V
                      (@NegZeroClass.toZero.{p2m_u_2} V
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_2} V
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_2} V
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_2} V
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_2} V inst_4)))))))) →
              ∀
                (embH :
                  @AddMonoidHom.{p2m_u_1, p2m_u_0} H G
                    (@AddZeroClass.toAddZero.{p2m_u_1} H
                      (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                        (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                          (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} G
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))),
                @Function.Injective.{p2m_u_1 + 1, p2m_u_0 + 1} H G
                    (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
                      (@AddMonoidHom.{p2m_u_1, p2m_u_0} H G
                        (@AddZeroClass.toAddZero.{p2m_u_1} H
                          (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                            (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                              (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
                        (@AddZeroClass.toAddZero.{p2m_u_0} G
                          (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                      H (fun x => G)
                      (@AddMonoidHom.instFunLike.{p2m_u_1, p2m_u_0} H G
                        (@AddZeroClass.toAddZero.{p2m_u_1} H
                          (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                            (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                              (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
                        (@AddZeroClass.toAddZero.{p2m_u_0} G
                          (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                      embH) →
                  ∀
                    (embV :
                      @AddMonoidHom.{p2m_u_2, p2m_u_0} V G
                        (@AddZeroClass.toAddZero.{p2m_u_2} V
                          (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                            (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                              (@AddGroup.toSubNegMonoid.{p2m_u_2} V (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                        (@AddZeroClass.toAddZero.{p2m_u_0} G
                          (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))),
                    @Function.Injective.{p2m_u_2 + 1, p2m_u_0 + 1} V G
                        (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_2 + 1, p2m_u_0 + 1}
                          (@AddMonoidHom.{p2m_u_2, p2m_u_0} V G
                            (@AddZeroClass.toAddZero.{p2m_u_2} V
                              (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                  (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                    (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                          V (fun x => G)
                          (@AddMonoidHom.instFunLike.{p2m_u_2, p2m_u_0} V G
                            (@AddZeroClass.toAddZero.{p2m_u_2} V
                              (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                  (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                    (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                          embV) →
                      ∀
                        (bank :
                          Fin k →
                            @AddChar.{p2m_u_0, 0} G
                              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                              Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                        (x y z : G),
                        @Eq.{1} Nat
                            (@Finset.card.{p2m_u_0} G
                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                  (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                  (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                    (@Finset.instSingleton.{p2m_u_0} G) z))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                          Or
                            (@Exists.{p2m_u_0 + 1} G fun d =>
                              And
                                (@Ne.{p2m_u_0 + 1} G d
                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                    (@Zero.toOfNat0.{p2m_u_0} G
                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                                (And
                                  (@Eq.{p2m_u_0 + 1} G
                                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                      (@instHAdd.{p2m_u_0} G
                                        (@AddCommMagma.toAdd.{p2m_u_0} G
                                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                      d d)
                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                      (@Zero.toOfNat0.{p2m_u_0} G
                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                                  (And
                                    (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                        (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                          (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                            (@Finset.instSingleton.{p2m_u_0} G) z)))
                                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                        (@Finset.instInsert.{p2m_u_0} G inst_1)
                                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                          (@instHAdd.{p2m_u_0} G
                                            (@AddCommMagma.toAdd.{p2m_u_0} G
                                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                          x d)
                                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                          (@Finset.instInsert.{p2m_u_0} G inst_1)
                                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                            (@instHAdd.{p2m_u_0} G
                                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                            y d)
                                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                            (@Finset.instSingleton.{p2m_u_0} G)
                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                              (@instHAdd.{p2m_u_0} G
                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                              z d)))))
                                    (And
                                      (∀ (q : G),
                                        @Eq.{1} Nat
                                          (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                              (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                  (@Finset.instSingleton.{p2m_u_0} G) z)))
                                            q)
                                          (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                                              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                (@instHAdd.{p2m_u_0} G
                                                  (@AddCommMagma.toAdd.{p2m_u_0} G
                                                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                x d)
                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                  (@instHAdd.{p2m_u_0} G
                                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                  y d)
                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                  (@Finset.instSingleton.{p2m_u_0} G)
                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                    (@instHAdd.{p2m_u_0} G
                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                    z d))))
                                            q))
                                      (∀ (i : Fin k),
                                        @Eq.{1} Complex
                                          (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, 0} G Complex Complex.commRing
                                            (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                                              (@AddChar.{p2m_u_0, 0} G
                                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                              G (fun x => Complex)
                                              (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                              (bank i))
                                            x y z)
                                          (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, 0} G Complex Complex.commRing
                                            (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                                              (@AddChar.{p2m_u_0, 0} G
                                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                              G (fun x => Complex)
                                              (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                              (bank i))
                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                              (@instHAdd.{p2m_u_0} G
                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                              x d)
                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                              (@instHAdd.{p2m_u_0} G
                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                              y d)
                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                              (@instHAdd.{p2m_u_0} G
                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                              z d)))))))
                            (@Exists.{p2m_u_0 + 1} G fun d =>
                              @Exists.{p2m_u_0 + 1} G fun v =>
                                And
                                  (@Ne.{p2m_u_0 + 1} G d
                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                      (@Zero.toOfNat0.{p2m_u_0} G
                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                                  (And
                                    (@Eq.{p2m_u_0 + 1} G
                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                        (@instHAdd.{p2m_u_0} G
                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                        d d)
                                      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                        (@Zero.toOfNat0.{p2m_u_0} G
                                          (@NegZeroClass.toZero.{p2m_u_0} G
                                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                                    (And
                                      (@Ne.{p2m_u_0 + 1} G v
                                        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                          (@Zero.toOfNat0.{p2m_u_0} G
                                            (@NegZeroClass.toZero.{p2m_u_0} G
                                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                                      (And
                                        (@Eq.{p2m_u_0 + 1} G
                                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                            (@instHAdd.{p2m_u_0} G
                                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                              (@instHAdd.{p2m_u_0} G
                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                              v v)
                                            v)
                                          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                            (@Zero.toOfNat0.{p2m_u_0} G
                                              (@NegZeroClass.toZero.{p2m_u_0} G
                                                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                                        (And
                                          (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                (@Zero.toOfNat0.{p2m_u_0} G
                                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                (@Finset.instInsert.{p2m_u_0} G inst_1) v
                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                  (@Finset.instSingleton.{p2m_u_0} G)
                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                    (@instHAdd.{p2m_u_0} G
                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                    v d))))
                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                (@Zero.toOfNat0.{p2m_u_0} G
                                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                (@Neg.neg.{p2m_u_0} G
                                                  (@NegZeroClass.toNeg.{p2m_u_0} G
                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                                  v)
                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                  (@Finset.instSingleton.{p2m_u_0} G)
                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                    (@instHAdd.{p2m_u_0} G
                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                    (@Neg.neg.{p2m_u_0} G
                                                      (@NegZeroClass.toNeg.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))
                                                      v)
                                                    d)))))
                                          (And
                                            (∀ (q : G),
                                              @Eq.{1} Nat
                                                (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                    (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                      (@Zero.toOfNat0.{p2m_u_0} G
                                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                  inst)))))))
                                                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                      (@Finset.instInsert.{p2m_u_0} G inst_1) v
                                                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                        (@Finset.instSingleton.{p2m_u_0} G)
                                                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                          (@instHAdd.{p2m_u_0} G
                                                            (@AddCommMagma.toAdd.{p2m_u_0} G
                                                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                          v d))))
                                                  q)
                                                (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                    (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                      (@Zero.toOfNat0.{p2m_u_0} G
                                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                  inst)))))))
                                                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                      (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                      (@Neg.neg.{p2m_u_0} G
                                                        (@NegZeroClass.toNeg.{p2m_u_0} G
                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                  inst)))))
                                                        v)
                                                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                        (@Finset.instSingleton.{p2m_u_0} G)
                                                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                          (@instHAdd.{p2m_u_0} G
                                                            (@AddCommMagma.toAdd.{p2m_u_0} G
                                                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                          (@Neg.neg.{p2m_u_0} G
                                                            (@NegZeroClass.toNeg.{p2m_u_0} G
                                                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                    G
                                                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                      inst)))))
                                                            v)
                                                          d))))
                                                  q))
                                            (∀ (i : Fin k),
                                              @Eq.{1} Complex
                                                (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, 0} G Complex
                                                  Complex.commRing
                                                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                                                    (@AddChar.{p2m_u_0, 0} G
                                                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                                    G (fun x => Complex)
                                                    (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                                                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                      (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                                    (bank i))
                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))))
                                                  v
                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                    (@instHAdd.{p2m_u_0} G
                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                    v d))
                                                (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, 0} G Complex
                                                  Complex.commRing
                                                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                                                    (@AddChar.{p2m_u_0, 0} G
                                                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                                    G (fun x => Complex)
                                                    (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                                                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                                      (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                                    (bank i))
                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))))
                                                  (@Neg.neg.{p2m_u_0} G
                                                    (@NegZeroClass.toNeg.{p2m_u_0} G
                                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                                    v)
                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                    (@instHAdd.{p2m_u_0} G
                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                    (@Neg.neg.{p2m_u_0} G
                                                      (@NegZeroClass.toNeg.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))
                                                      v)
                                                    d))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_complex_character_bank_collision

