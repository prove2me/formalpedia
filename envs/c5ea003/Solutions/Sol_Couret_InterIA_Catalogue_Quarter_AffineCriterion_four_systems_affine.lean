-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.AffineCriterion.four_systems_affine
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:54:07.122346+00:00
-- url     : https://prove2.me/submissions/d457fb7a-99b2-4354-88fb-cc5798f27546

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_witness_of_images
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm













theorem p2m_local_four_systems_affine (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (u : (ZMod (4*q))ˣ) (hu : FourSystems q x u) :
    AffineEquivalent (patternA q x) (patternB q x) := by
  rcases hu with ⟨hQ,hX⟩|⟨hQ,hX⟩
  · refine ⟨u,0,affine_witness_of_images q hq x hx u 0 ?_ ?_ ?_⟩
    · left; simp
    · right; simpa only [add_zero] using hQ
    · simpa only [add_zero] using hX
  · refine ⟨u,q,affine_witness_of_images q hq x hx u q ?_ ?_ ?_⟩
    · right; simp
    · left; rw [hQ,neg_add_cancel]
    · rcases hX with hX|hX
      · left; rw [hX]
      · right; rw [hX]; abel





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
        ∀
          (u :
            @Units.{0}
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))))),
          Couret.InterIA.Catalogue.Quarter.AffineCriterion.FourSystems q x u →
            @Couret.InterIA.NormalForm.AffineEquivalent
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
              (Couret.InterIA.Catalogue.Quarter.patternA q x) (Couret.InterIA.Catalogue.Quarter.patternB q x) := @_root_.Couret.InterIA.Catalogue.Quarter.AffineCriterion.p2m_local_four_systems_affine

