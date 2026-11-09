-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Primitive.gcd_reference_reduction
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:24.936716+00:00
-- url     : https://prove2.me/submissions/51a7d70b-255e-4a26-bece-a220dbd3b477

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_gcd_support_reduction
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_normalise_negative
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_unit_quarter_sign
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter.AffineCriterion



theorem normalise_positive (q : ℕ) (x : ZMod (4*q)) (u : (ZMod (4*q))ˣ)
    (huq : (u : ZMod (4*q))*q=q) (hux : (u : ZMod (4*q))*x=1) :
    (patternA q x).image (fun z => (u : ZMod (4*q))*z)=patternA q 1 ∧
    (patternB q x).image (fun z => (u : ZMod (4*q))*z)=patternB q 1 := by
  have h2 : (u : ZMod (4*q))*(x+2 • (q : ZMod (4*q)))=1+2 • (q : ZMod (4*q)) := by
    simp only [nsmul_eq_mul]; linear_combination hux+2*huq
  have h1 : (u : ZMod (4*q))*(x+q)=1+q := by linear_combination hux+huq
  have h3 : (u : ZMod (4*q))*(x+3 • (q : ZMod (4*q)))=1+3 • (q : ZMod (4*q)) := by
    simp only [nsmul_eq_mul]; linear_combination hux+3*huq
  simp only [patternA,patternB,image_insert,image_singleton,mul_zero,huq,hux,h2,h1,h3]
  constructor <;> trivial



/-- A common affine map reaches the reference pair, with its orientation stated. -/
theorem unit_parameter_reference_pair (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : IsUnit x) :
    ∃ u : (ZMod (4*q))ˣ, ∃ v : ZMod (4*q),
      ((patternA q x).image (fun z => (u : ZMod (4*q))*z+v)=patternA q 1 ∧
       (patternB q x).image (fun z => (u : ZMod (4*q))*z+v)=patternB q 1) ∨
      ((patternA q x).image (fun z => (u : ZMod (4*q))*z+v)=patternB q 1 ∧
       (patternB q x).image (fun z => (u : ZMod (4*q))*z+v)=patternA q 1) := by
  obtain ⟨a,rfl⟩ := hx
  have hua : (a⁻¹ : (ZMod (4*q))ˣ)*(a : ZMod (4*q))=1 := by simp
  rcases unit_quarter_sign q hq a⁻¹ with hp|hn
  · exact ⟨a⁻¹,0,Or.inl (by simpa only [add_zero] using normalise_positive q a a⁻¹ hp hua)⟩
  · exact ⟨a⁻¹,q,Or.inr (normalise_negative q a a⁻¹ hn hua)⟩

/-- Common-factor reduction followed by a common affine normalisation in the smaller group. -/
theorem p2m_local_gcd_reference_reduction (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (hna : ¬ AffineEquivalent (patternA q x) (patternB q x)) :
    ∃ d b a : ℕ, 0 < d ∧ 0 < b ∧ q=d*b ∧ x.val=d*a ∧ a.Coprime b ∧ b%4=2 ∧
      (patternA b (a : ZMod (4*b))).image (dilate (4*q) d)=patternA q x ∧
      (patternB b (a : ZMod (4*b))).image (dilate (4*q) d)=patternB q x ∧
      ∃ u : (ZMod (4*b))ˣ, ∃ v : ZMod (4*b),
        ((patternA b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternA b 1 ∧
         (patternB b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternB b 1) ∨
        ((patternA b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternB b 1 ∧
         (patternB b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternA b 1) := by
  obtain ⟨d,b,a,hd,hb,hq',hx',hc,hm,hu,hA,hB⟩ := gcd_support_reduction q hq x hx hna
  exact ⟨d,b,a,hd,hb,hq',hx',hc,hm,hA,hB,unit_parameter_reference_pair b hb a hu⟩

end Couret.InterIA.Catalogue.Quarter.Primitive

theorem solution : ∀ (q : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
    ∀
      (x :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)),
      Not
          (@Membership.mem.{0, 0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
            (Finset.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Finset.instSetLike.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))
            (Couret.InterIA.Catalogue.Quarter.badParameters q) x) →
        Not
            (@Couret.InterIA.NormalForm.AffineEquivalent
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
              (Couret.InterIA.Catalogue.Quarter.patternA q x) (Couret.InterIA.Catalogue.Quarter.patternB q x)) →
          @Exists.{1} Nat fun d =>
            @Exists.{1} Nat fun b =>
              @Exists.{1} Nat fun a =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
                  (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
                    (And (@Eq.{1} Nat q (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b))
                      (And
                        (@Eq.{1} Nat
                          (@ZMod.val
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                            x)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d a))
                        (And (Nat.Coprime a b)
                          (And
                            (@Eq.{1} Nat
                              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (And
                              (@Eq.{1}
                                (Finset.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
                                (@Finset.image.{0, 0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                  (ZMod.decidableEq
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                  (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                                    d
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                  (Couret.InterIA.Catalogue.Quarter.patternA b
                                    (@Nat.cast.{0}
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                      (@AddMonoidWithOne.toNatCast.{0}
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                          (@Ring.toAddGroupWithOne.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (@CommRing.toRing.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                              (ZMod.commRing
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))))))
                                      a)))
                                (Couret.InterIA.Catalogue.Quarter.patternA q x))
                              (And
                                (@Eq.{1}
                                  (Finset.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
                                  (@Finset.image.{0, 0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                    (ZMod.decidableEq
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                    (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                                      d
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (Couret.InterIA.Catalogue.Quarter.patternB b
                                      (@Nat.cast.{0}
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                        (@AddMonoidWithOne.toNatCast.{0}
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod.commRing
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b))))))
                                        a)))
                                  (Couret.InterIA.Catalogue.Quarter.patternB q x))
                                (@Exists.{1}
                                  (@Units.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (@Semiring.toMonoid.{0}
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                      (@CommSemiring.toSemiring.{0}
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                        (@CommRing.toCommSemiring.{0}
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                          (ZMod.commRing
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))))))
                                  fun u =>
                                  @Exists.{1}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    fun v =>
                                    Or
                                      (And
                                        (@Eq.{1}
                                          (Finset.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b)))
                                          (@Finset.image.{0, 0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod.decidableEq
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (fun z =>
                                              @HAdd.hAdd.{0, 0, 0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@instHAdd.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@Distrib.toAdd.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@instDistribOfSemiring.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))))
                                                (@HMul.hMul.{0, 0, 0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@instHMul.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Distrib.toMul.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@instDistribOfSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommSemiring.toSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (@CommRing.toCommSemiring.{0}
                                                            (ZMod
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b))
                                                            (ZMod.commRing
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b)))))))
                                                  (@Units.val.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Semiring.toMonoid.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))
                                                    u)
                                                  z)
                                                v)
                                            (Couret.InterIA.Catalogue.Quarter.patternA b
                                              (@Nat.cast.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toNatCast.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))
                                                a)))
                                          (Couret.InterIA.Catalogue.Quarter.patternA b
                                            (@OfNat.ofNat.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                              (nat_lit 1)
                                              (@One.toOfNat1.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toOne.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))))))
                                        (@Eq.{1}
                                          (Finset.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b)))
                                          (@Finset.image.{0, 0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod.decidableEq
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (fun z =>
                                              @HAdd.hAdd.{0, 0, 0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@instHAdd.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@Distrib.toAdd.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@instDistribOfSemiring.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))))
                                                (@HMul.hMul.{0, 0, 0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@instHMul.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Distrib.toMul.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@instDistribOfSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommSemiring.toSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (@CommRing.toCommSemiring.{0}
                                                            (ZMod
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b))
                                                            (ZMod.commRing
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b)))))))
                                                  (@Units.val.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Semiring.toMonoid.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))
                                                    u)
                                                  z)
                                                v)
                                            (Couret.InterIA.Catalogue.Quarter.patternB b
                                              (@Nat.cast.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toNatCast.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))
                                                a)))
                                          (Couret.InterIA.Catalogue.Quarter.patternB b
                                            (@OfNat.ofNat.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                              (nat_lit 1)
                                              (@One.toOfNat1.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toOne.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b)))))))))))
                                      (And
                                        (@Eq.{1}
                                          (Finset.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b)))
                                          (@Finset.image.{0, 0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod.decidableEq
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (fun z =>
                                              @HAdd.hAdd.{0, 0, 0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@instHAdd.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@Distrib.toAdd.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@instDistribOfSemiring.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))))
                                                (@HMul.hMul.{0, 0, 0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@instHMul.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Distrib.toMul.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@instDistribOfSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommSemiring.toSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (@CommRing.toCommSemiring.{0}
                                                            (ZMod
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b))
                                                            (ZMod.commRing
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b)))))))
                                                  (@Units.val.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Semiring.toMonoid.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))
                                                    u)
                                                  z)
                                                v)
                                            (Couret.InterIA.Catalogue.Quarter.patternA b
                                              (@Nat.cast.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toNatCast.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))
                                                a)))
                                          (Couret.InterIA.Catalogue.Quarter.patternB b
                                            (@OfNat.ofNat.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                              (nat_lit 1)
                                              (@One.toOfNat1.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toOne.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))))))
                                        (@Eq.{1}
                                          (Finset.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b)))
                                          (@Finset.image.{0, 0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (ZMod.decidableEq
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                            (fun z =>
                                              @HAdd.hAdd.{0, 0, 0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@instHAdd.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@Distrib.toAdd.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@instDistribOfSemiring.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))))
                                                (@HMul.hMul.{0, 0, 0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@instHMul.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Distrib.toMul.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@instDistribOfSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommSemiring.toSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (@CommRing.toCommSemiring.{0}
                                                            (ZMod
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b))
                                                            (ZMod.commRing
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b)))))))
                                                  (@Units.val.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Semiring.toMonoid.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b)))))
                                                    u)
                                                  z)
                                                v)
                                            (Couret.InterIA.Catalogue.Quarter.patternB b
                                              (@Nat.cast.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toNatCast.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))
                                                a)))
                                          (Couret.InterIA.Catalogue.Quarter.patternA b
                                            (@OfNat.ofNat.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                              (nat_lit 1)
                                              (@One.toOfNat1.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                (@AddMonoidWithOne.toOne.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b))
                                                    (@Ring.toAddGroupWithOne.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b))
                                                      (@CommRing.toRing.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))
                                                        (ZMod.commRing
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b))))))))))))))))))) := @_root_.Couret.InterIA.Catalogue.Quarter.Primitive.p2m_local_gcd_reference_reduction

