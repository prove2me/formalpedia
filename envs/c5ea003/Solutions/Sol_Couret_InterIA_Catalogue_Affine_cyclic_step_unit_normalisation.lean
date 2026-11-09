-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Affine.cyclic_step_unit_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:59.585886+00:00
-- url     : https://prove2.me/submissions/98339bda-d122-4b8a-b71d-a5f69d890443

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_unit_mul_add_order
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts



/-- Reuses Mathlib's divisor/unit theorem, including its justified unit lifting. -/
theorem p2m_local_cyclic_step_unit_normalisation (n : ℕ) (hn : 0 < n) (r : ZMod n) (k : ℕ)
    (ho : addOrderOf r=k) :
    ∃ q : ℕ, 0 < q ∧ n=k*q ∧ ∃ u : (ZMod n)ˣ, r=(u : ZMod n)*(q : ZMod n) := by
  obtain ⟨d,hd,u,hu,hr⟩ := ZMod.eq_unit_mul_divisor r
  let U : (ZMod n)ˣ := hu.unit
  have hr' : r=(U : ZMod n)*(d : ZMod n) := by simpa only [IsUnit.unit_spec] using hr
  have hg : n.gcd d=d := Nat.gcd_eq_right_iff_dvd.mpr hd
  have hdo : addOrderOf (d : ZMod n)=n/d := by rw [ZMod.addOrderOf_coe d (by omega),hg]
  have hdiv : n/d=k := by
    rw [← hdo,← unit_mul_add_order n U (d : ZMod n),← hr']
    exact ho
  have hnd : n=k*d := by simpa only [hdiv] using (Nat.div_mul_cancel hd).symm
  have hdpos : 0 < d := by
    by_contra h
    have hz : d=0 := by omega
    rw [hz,mul_zero] at hnd
    omega
  exact ⟨d,hdpos,hnd,U,hr'⟩





end Couret.InterIA.Catalogue.Affine

theorem solution : ∀ (n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (r : ZMod n) (k : Nat),
      @Eq.{1} Nat
          (@addOrderOf.{0} (ZMod n)
            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
            r)
          k →
        @Exists.{1} Nat fun q =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
            (And (@Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k q))
              (@Exists.{1}
                (@Units.{0} (ZMod n)
                  (@Semiring.toMonoid.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
                fun u =>
                @Eq.{1} (ZMod n) r
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
                    (@Nat.cast.{0} (ZMod n)
                      (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                      q)))) := @_root_.Couret.InterIA.Catalogue.Affine.p2m_local_cyclic_step_unit_normalisation

