-- Prove2me | solution 1 for Couret.STROBO2TORS.paired_partner_fixed_source
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:16.554072+00:00
-- url     : https://prove2.me/submissions/03e90a72-9082-4889-8aa5-774c56d33d7c

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



















/-- Keeps the reflection tied to the specified source, rather than an existential relabelling. -/
theorem p2m_local_paired_partner_fixed_source (S T : Finset G)
    (a b t c d e : G) (hS : S.card = 3) (hT : T.card = 3)
    (hd : d + d = 0) (he : e + e = 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b) (htc : t + t ≠ c + c)
    (hs : S = {a, b, b + d}) (ht : T = {t, c, c + e})
    (hsq : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    OrdinaryPartner S T ∨
      ((((b - a) + (b - a)) + (b - a) = 0 ∨
         ((b - a) + (b - a)) + (b - a) = d) ∧
        OrdinaryPartner ({a, b + b - a, (b + b - a) + d} : Finset G) T) := by
  have hexp := explicit_square_eq_of_orderedSquare_eq S T a b (b + d) t c (c + e)
    hS hT hs ht hsq
  obtain ⟨u, hu, htu, hed, hcases⟩ :=
    paired_square_classification_after_normalization a b t c d e hd he he0 hab htc hexp
  have hlast : (c + e) + u = (c + u) + e := by abel
  have hnorm : translateSupport T u = ({a, c + u, (c + u) + d} : Finset G) := by
    rw [ht, translateSupport_three, htu, hlast, hed]
  rcases hcases with hdirect | ⟨hcross, h3⟩
  · left
    have hTS : translateSupport T u = S := by
      rw [hnorm, hs]
      rcases hdirect with h | h
      · rw [h]
      · rw [h]
        have hf : (b + d) + d = b := by simp [add_assoc, hd]
        rw [hf]; exact support_swap_last a (b + d) b
    exact ⟨u, hu, translateSupport_eq_of_reverse S T u hu hTS⟩
  · right
    have hTR : translateSupport T u =
        ({a, b + b - a, (b + b - a) + d} : Finset G) := by
      rw [hnorm]
      rcases hcross with h | h
      · rw [h]
      · rw [h]
        have hf : ((b + b - a) + d) + d = b + b - a := by simp [add_assoc, hd]
        rw [hf]; exact support_swap_last a ((b + b - a) + d) (b + b - a)
    exact ⟨h3, u, hu, translateSupport_eq_of_reverse _ T u hu hTR⟩



section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (S T : Finset.{p2m_u_0} G)
  (a b t c d e : G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            d d)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Eq.{p2m_u_0 + 1} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              e e)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          @Ne.{p2m_u_0 + 1} G e
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
            @Ne.{p2m_u_0 + 1} G
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  a a)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  b b) →
              @Ne.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    t t)
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    c c) →
                @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S
                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                        b
                        (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                          (@Finset.instSingleton.{p2m_u_0} G)
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            b d)))) →
                  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                        t
                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                          (@Finset.instInsert.{p2m_u_0} G inst_1) c
                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instSingleton.{p2m_u_0} G)
                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                              (@instHAdd.{p2m_u_0} G
                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                              c e)))) →
                    (∀ (z : G),
                        @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
                          (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z)) →
                      Or (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S T)
                        (And
                          (Or
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
                                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHSub.{p2m_u_0} G
                                      (@SubNegMonoid.toSub.{p2m_u_0} G
                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                    b a)
                                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHSub.{p2m_u_0} G
                                      (@SubNegMonoid.toSub.{p2m_u_0} G
                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                    b a))
                                (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                  (@instHSub.{p2m_u_0} G
                                    (@SubNegMonoid.toSub.{p2m_u_0} G
                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                  b a))
                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                (@Zero.toOfNat0.{p2m_u_0} G
                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
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
                                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHSub.{p2m_u_0} G
                                      (@SubNegMonoid.toSub.{p2m_u_0} G
                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                    b a)
                                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHSub.{p2m_u_0} G
                                      (@SubNegMonoid.toSub.{p2m_u_0} G
                                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                    b a))
                                (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                  (@instHSub.{p2m_u_0} G
                                    (@SubNegMonoid.toSub.{p2m_u_0} G
                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                  b a))
                              d))
                          (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1
                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instInsert.{p2m_u_0} G inst_1) a
                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instInsert.{p2m_u_0} G inst_1)
                                (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                  (@instHSub.{p2m_u_0} G
                                    (@SubNegMonoid.toSub.{p2m_u_0} G
                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHAdd.{p2m_u_0} G
                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                    b b)
                                  a)
                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                  (@Finset.instSingleton.{p2m_u_0} G)
                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHAdd.{p2m_u_0} G
                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                    (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                      (@instHSub.{p2m_u_0} G
                                        (@SubNegMonoid.toSub.{p2m_u_0} G
                                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                            (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                        (@instHAdd.{p2m_u_0} G
                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                        b b)
                                      a)
                                    d))))
                            T)) := @_root_.Couret.STROBO2TORS.p2m_local_paired_partner_fixed_source

