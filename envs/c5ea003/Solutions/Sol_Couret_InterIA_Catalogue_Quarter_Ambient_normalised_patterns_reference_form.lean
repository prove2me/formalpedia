-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Ambient.normalised_patterns_reference_form
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:24:58.052573+00:00
-- url     : https://prove2.me/submissions/a90cb18f-a0c7-46a0-9808-4a598701f31f

import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_affine_image_comp
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_pattern_ambient_reference_pair
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive Couret.InterIA.Catalogue.Parameters
open Couret.InterIA.Catalogue.AffineTransport Couret.InterIA.Parity



theorem p2m_local_normalised_patterns_reference_form (n q : ℕ) (hn : n=4*q) (hq : 0 < q)
    (S T : Finset (ZMod n)) (u : (ZMod n)ˣ) (v x : ZMod n)
    (hx : x ∉ ({0,(q : ZMod n),2 • (q : ZMod n),3 • (q : ZMod n)} : Finset (ZMod n)))
    (hS : S.image (fun z => (u : ZMod n)*z+v)={0,(q : ZMod n),x,x+2 • (q : ZMod n)})
    (hT : T.image (fun z => (u : ZMod n)*z+v)={0,(q : ZMod n),x+q,x+3 • (q : ZMod n)})
    (hna : ¬ AffineEquivalent S T) : AmbientReferenceForm n S T := by
  subst n
  change x ∉ badParameters q at hx
  change S.image (fun z => (u : ZMod (4*q))*z+v)=patternA q x at hS
  change T.image (fun z => (u : ZMod (4*q))*z+v)=patternB q x at hT
  have hp : ¬ AffineEquivalent (patternA q x) (patternB q x) := by
    intro he
    apply hna
    apply (common_affine_equivalent_iff S T u v).mp
    rw [hS,hT]
    exact he
  obtain ⟨d,b,hd,hb,hq',hm,U,V,ho⟩ := pattern_ambient_reference_pair q hq x hx hp
  refine ⟨d,b,hd,hb,by rw [hq'],hm,U*u,(U : ZMod (4*q))*v+V,?_⟩
  have heS := affine_image_comp S u U v V
  have heT := affine_image_comp T u U v V
  rw [hS] at heS
  rw [hT] at heT
  rcases ho with ho|ho
  · exact Or.inl ⟨heS.symm.trans ho.1,heT.symm.trans ho.2⟩
  · exact Or.inr ⟨heS.symm.trans ho.1,heT.symm.trans ho.2⟩







end Couret.InterIA.Catalogue.Quarter.Ambient

theorem solution : ∀ (n q : Nat),
  @Eq.{1} Nat n
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
      ∀ (S T : Finset.{0} (ZMod n))
        (u :
          @Units.{0} (ZMod n)
            (@Semiring.toMonoid.{0} (ZMod n)
              (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
        (v x : ZMod n),
        Not
            (@Membership.mem.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (ZMod n)) (ZMod n) (@Finset.instSetLike.{0} (ZMod n)))
              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (ZMod n)
                    (@MulZeroClass.toZero.{0} (ZMod n)
                      (@instMulZeroClassOfSemiring.{0} (ZMod n)
                        (@CommSemiring.toSemiring.{0} (ZMod n)
                          (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                  (@Nat.cast.{0} (ZMod n)
                    (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                        (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                    q)
                  (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                    (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                    (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                      (@instHSMul.{0, 0} Nat (ZMod n)
                        (@AddMonoid.toNSMul.{0} (ZMod n)
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.cast.{0} (ZMod n)
                        (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                            (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                        q))
                    (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                      (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                        (@instHSMul.{0, 0} Nat (ZMod n)
                          (@AddMonoid.toNSMul.{0} (ZMod n)
                            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                  (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.cast.{0} (ZMod n)
                          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                          q))))))
              x) →
          @Eq.{1} (Finset.{0} (ZMod n))
              (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
                (fun z =>
                  @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                    (@instHAdd.{0} (ZMod n)
                      (@Distrib.toAdd.{0} (ZMod n)
                        (@instDistribOfSemiring.{0} (ZMod n)
                          (@CommSemiring.toSemiring.{0} (ZMod n)
                            (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                    (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                      (@instHMul.{0} (ZMod n)
                        (@Distrib.toMul.{0} (ZMod n)
                          (@instDistribOfSemiring.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                      (@Units.val.{0} (ZMod n)
                        (@Semiring.toMonoid.{0} (ZMod n)
                          (@CommSemiring.toSemiring.{0} (ZMod n)
                            (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
                        u)
                      z)
                    v)
                S)
              (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (ZMod n)
                    (@MulZeroClass.toZero.{0} (ZMod n)
                      (@instMulZeroClassOfSemiring.{0} (ZMod n)
                        (@CommSemiring.toSemiring.{0} (ZMod n)
                          (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                  (@Nat.cast.{0} (ZMod n)
                    (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                        (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                    q)
                  (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                    (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n)) x
                    (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                      (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                        (@instHAdd.{0} (ZMod n)
                          (@Distrib.toAdd.{0} (ZMod n)
                            (@instDistribOfSemiring.{0} (ZMod n)
                              (@CommSemiring.toSemiring.{0} (ZMod n)
                                (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                        x
                        (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                          (@instHSMul.{0, 0} Nat (ZMod n)
                            (@AddMonoid.toNSMul.{0} (ZMod n)
                              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                  (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                    (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.cast.{0} (ZMod n)
                            (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                  (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                            q))))))) →
            @Eq.{1} (Finset.{0} (ZMod n))
                (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
                  (fun z =>
                    @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                      (@instHAdd.{0} (ZMod n)
                        (@Distrib.toAdd.{0} (ZMod n)
                          (@instDistribOfSemiring.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                      (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                        (@instHMul.{0} (ZMod n)
                          (@Distrib.toMul.{0} (ZMod n)
                            (@instDistribOfSemiring.{0} (ZMod n)
                              (@CommSemiring.toSemiring.{0} (ZMod n)
                                (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                        (@Units.val.{0} (ZMod n)
                          (@Semiring.toMonoid.{0} (ZMod n)
                            (@CommSemiring.toSemiring.{0} (ZMod n)
                              (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
                          u)
                        z)
                      v)
                  T)
                (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                  (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                  (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (ZMod n)
                      (@MulZeroClass.toZero.{0} (ZMod n)
                        (@instMulZeroClassOfSemiring.{0} (ZMod n)
                          (@CommSemiring.toSemiring.{0} (ZMod n)
                            (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
                  (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                    (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                    (@Nat.cast.{0} (ZMod n)
                      (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                      q)
                    (@Insert.insert.{0, 0} (ZMod n) (Finset.{0} (ZMod n))
                      (@Finset.instInsert.{0} (ZMod n) (ZMod.decidableEq n))
                      (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                        (@instHAdd.{0} (ZMod n)
                          (@Distrib.toAdd.{0} (ZMod n)
                            (@instDistribOfSemiring.{0} (ZMod n)
                              (@CommSemiring.toSemiring.{0} (ZMod n)
                                (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                        x
                        (@Nat.cast.{0} (ZMod n)
                          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                          q))
                      (@Singleton.singleton.{0, 0} (ZMod n) (Finset.{0} (ZMod n)) (@Finset.instSingleton.{0} (ZMod n))
                        (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                          (@instHAdd.{0} (ZMod n)
                            (@Distrib.toAdd.{0} (ZMod n)
                              (@instDistribOfSemiring.{0} (ZMod n)
                                (@CommSemiring.toSemiring.{0} (ZMod n)
                                  (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                          x
                          (@HSMul.hSMul.{0, 0, 0} Nat (ZMod n) (ZMod n)
                            (@instHSMul.{0, 0} Nat (ZMod n)
                              (@AddMonoid.toNSMul.{0} (ZMod n)
                                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                    (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                      (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.cast.{0} (ZMod n)
                              (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                                  (@Ring.toAddGroupWithOne.{0} (ZMod n)
                                    (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                              q))))))) →
              Not (@Couret.InterIA.NormalForm.AffineEquivalent n S T) →
                Couret.InterIA.Catalogue.Quarter.Ambient.AmbientReferenceForm n S T := @_root_.Couret.InterIA.Catalogue.Quarter.Ambient.p2m_local_normalised_patterns_reference_form

