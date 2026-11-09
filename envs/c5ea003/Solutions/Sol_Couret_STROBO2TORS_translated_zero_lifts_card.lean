-- Prove2me | solution 1 for Couret.STROBO2TORS.translated_zero_lifts_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:46.799149+00:00
-- url     : https://prove2.me/submissions/b35a7409-e132-48b2-b13e-b1588b2dd2a1

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_zero_lifts_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]



omit [Fintype G] in
/-- Translation commutes with the canonical singleton parameter. -/
theorem translate_paramSupport (a d v u : G) :
    translateSupport (paramSupport ((a,d),v)) u = paramSupport ((a+u,d),v) := by
  simp only [paramSupport, translateSupport_three]
  congr 2 <;> abel_nf





/-- For any fixed translation u, exactly three singleton positions put zero
in the translated support. This statement does not assume u is in H. -/
theorem p2m_local_translated_zero_lifts_card (d v u : G)
    (hd : d+d=0) (hd0 : d ≠ 0) (hv : (v+v)+v=0) (hv0 : v ≠ 0) :
    ((Finset.univ : Finset G).filter
      (fun a => 0 ∈ translateSupport (paramSupport ((a,d),v)) u)).card = 3 := by
  have he : ((Finset.univ : Finset G).filter
      (fun a => 0 ∈ translateSupport (paramSupport ((a,d),v)) u)) =
      (((Finset.univ : Finset G).filter (fun a => 0 ∈ paramSupport ((a,d),v))).image
        (fun a => a-u)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      translate_paramSupport]
    constructor
    · intro h
      exact ⟨a+u,h,by abel⟩
    · rintro ⟨b,h,hba⟩
      have hb : a+u=b := by rw [← hba]; abel
      rwa [hb]
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => sub_left_inj.mp h)]
  exact paramSupport_zero_lifts_card d v hd hd0 hv hv0






















attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (d v u : G),
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
    @Ne.{p2m_u_0 + 1} G d
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
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              v v)
            v)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Ne.{p2m_u_0 + 1} G v
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@Finset.filter.{p2m_u_0} G
                (fun a =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                      (@Finset.instSetLike.{p2m_u_0} G))
                    (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
                      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                          (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v))
                      u)
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (fun a =>
                  @Finset.decidableMem.{p2m_u_0} G inst_1
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                    (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
                      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                          (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v))
                      u))
                (@Finset.univ.{p2m_u_0} G inst_2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) := @_root_.Couret.STROBO2TORS.p2m_local_translated_zero_lifts_card

