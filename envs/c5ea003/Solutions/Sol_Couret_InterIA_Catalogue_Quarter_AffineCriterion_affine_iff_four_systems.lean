-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_iff_four_systems
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:45.519325+00:00
-- url     : https://prove2.me/submissions/435074f9-d4a2-4779-bd42-5f4b331f8da4

import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_common_pair_cases
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_exchanged_point_image
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_four_systems_affine
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm











theorem affine_implies_four_systems (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (u : (ZMod (4*q))ˣ) (v : ZMod (4*q))
    (hAB : (patternA q x).image (fun a => (u : ZMod (4*q))*a+v)=patternB q x) :
    FourSystems q x u := by
  have hc := affine_common_pair_cases q hq x hx u v hAB
  have he := affine_exchanged_point_image q hq x hx u v hAB
  rcases hc with ⟨rfl,hu⟩|⟨rfl,hu⟩
  · exact Or.inl ⟨hu,by simpa only [add_zero] using he⟩
  · refine Or.inr ⟨hu,?_⟩
    rcases he with he|he
    · exact Or.inl (add_right_cancel he)
    · right
      calc (u : ZMod (4*q))*x=((u : ZMod (4*q))*x+q)-q := by abel
           _=x+2 • (q : ZMod (4*q)) := by rw [he]; abel



/-- Exhaustive criterion; x is never required to be a unit. -/
theorem p2m_local_affine_iff_four_systems (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    AffineEquivalent (patternA q x) (patternB q x) ↔
      ∃ u : (ZMod (4*q))ˣ, FourSystems q x u := by
  constructor
  · rintro ⟨u,v,hAB⟩
    exact ⟨u,affine_implies_four_systems q hq x hx u v hAB⟩
  · rintro ⟨u,hu⟩
    exact four_systems_affine q hq x hx u hu



end Couret.InterIA.Catalogue.Quarter.AffineCriterion

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
        Iff
          (@Couret.InterIA.NormalForm.AffineEquivalent
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
            (Couret.InterIA.Catalogue.Quarter.patternA q x) (Couret.InterIA.Catalogue.Quarter.patternB q x))
          (@Exists.{1}
            (@Units.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Semiring.toMonoid.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                (@CommSemiring.toSemiring.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                  (@CommRing.toCommSemiring.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))))
            fun u => Couret.InterIA.Catalogue.Quarter.AffineCriterion.FourSystems q x u) := @_root_.Couret.InterIA.Catalogue.Quarter.AffineCriterion.p2m_local_affine_iff_four_systems

