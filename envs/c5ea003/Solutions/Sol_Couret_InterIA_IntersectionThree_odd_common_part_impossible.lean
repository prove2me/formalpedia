-- Prove2me | solution 1 for Couret.InterIA.IntersectionThree.odd_common_part_impossible
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:21.286961+00:00
-- url     : https://prove2.me/submissions/25fc6283-e31c-44fb-a9d4-8d84c2161041

import Definitions.Def_Couret_IntersectionThree_e6b918e458b3
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
import Definitions.Def_Couret_TranslationControls_1ed5eea33a54

set_option autoImplicit false
namespace Couret.InterIA.IntersectionThree
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







theorem p2m_local_odd_common_part_impossible (C : Finset G) (a h : G)
    (hh : h ≠ 0) (hh2 : h+h=0) (ha : a ∉ C) (hb : a+h ∉ C)
    (hodd : C.card % 2 = 1)
    (hsquare : ∀ z, orderedSquare (insert a C) z = orderedSquare (insert (a+h) C) z) :
    False := by
  have hc := twice_fibres_card h hh hh2 C (common_part_stable C a h hh2 ha hb hsquare)
  omega

end Couret.InterIA.IntersectionThree

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (C : Finset.{p2m_u_0} G)
  (a h : G),
  @Ne.{p2m_u_0 + 1} G h
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
          h h)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      Not
          (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) C a) →
        Not
            (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) C
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a h)) →
          @Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@Finset.card.{p2m_u_0} G C)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            (∀ (z : G),
                @Eq.{1} Nat
                  (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
                      C)
                    z)
                  (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a h)
                      C)
                    z)) →
              False := @_root_.Couret.InterIA.IntersectionThree.p2m_local_odd_common_part_impossible

