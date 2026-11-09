-- Prove2me | solution 1 for Couret.InterIA.TwoPoint.cardinal_two_collision_is_translation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:33:19.210024+00:00
-- url     : https://prove2.me/submissions/5dbe41e7-f63e-4b1d-91cd-4cab8b982432

import Definitions.Def_Couret_TwoPointCollision_eefa36a5b454
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_TwoPoint_distinct_doubles_gap
import Theorems.Thm_Couret_InterIA_TwoPoint_equal_doubles_gap
import Theorems.Thm_Couret_InterIA_TwoPoint_gap_produces_translation
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.TwoPoint
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



























theorem pair_profiles_force_gap (a b c d : G) (hab : a ≠ b) (hcd : c ≠ d)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    d-c=b-a ∨ c-d=b-a := by
  by_cases hd : a+a=b+b
  · exact equal_doubles_gap a b c d hab hcd hd heq
  · exact distinct_doubles_gap a b c d hab hd heq



/-- Equality of actual ordered squares of two distinct-point pairs forces translation. -/
theorem two_point_collision_is_translation (a b c d : G)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hsquare : ∀ z, orderedSquare ({a,b} : Finset G) z=
      orderedSquare ({c,d} : Finset G) z) :
    ∃ t : G, ({a,b} : Finset G).image (fun x => x+t)=({c,d} : Finset G) := by
  apply gap_produces_translation a b c d
  apply pair_profiles_force_gap a b c d hab hcd
  intro z
  simpa only [actual_pair_coefficient a b z hab,actual_pair_coefficient c d z hcd] using hsquare z

/-- Intrinsic support formulation; no enumeration or bound on the ambient group. -/
theorem p2m_local_cardinal_two_collision_is_translation (S T : Finset G)
    (hS : S.card=2) (hT : T.card=2)
    (hsquare : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∃ t : G, S.image (fun x => x+t)=T := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  obtain ⟨c,d,hcd,rfl⟩ := Finset.card_eq_two.mp hT
  exact two_point_collision_is_translation a b c d hab hcd hsquare

end Couret.InterIA.TwoPoint

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      (∀ (z : G),
          @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 S z)
            (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 T z)) →
        @Exists.{p2m_u_0 + 1} G fun t =>
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (@Finset.image.{p2m_u_0, p2m_u_0} G G inst_1
              (fun x =>
                @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  x t)
              S)
            T := @_root_.Couret.InterIA.TwoPoint.p2m_local_cardinal_two_collision_is_translation

