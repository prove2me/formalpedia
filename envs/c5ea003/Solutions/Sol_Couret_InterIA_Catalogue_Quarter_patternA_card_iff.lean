-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.patternA_card_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:58.081686+00:00
-- url     : https://prove2.me/submissions/7e0796ee-2fa1-4330-abe9-996b259cf2a7

import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
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
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_two_pattern_parameter_separation
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_pair_separations
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_quarter_ne_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_two_quarters_ne_zero
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Catalogue.Parameters Couret.InterIA.Parity



















theorem p2m_local_patternA_card_iff (q : ℕ) (hq : 0 < q) (x : ZMod (4*q)) :
    (patternA q x).card=4 ↔ x ∉ badParameters q := by
  constructor
  · intro hc
    exact two_pattern_parameter_separation (4*q) q rfl x hc
  · intro hx
    obtain ⟨hx0,hxq,hx20,hx2q⟩ := admissible_pair_separations q x hx
    apply Finset.card_eq_four.mpr
    refine ⟨0,q,x,x+2 • (q : ZMod (4*q)),Ne.symm (quarter_ne_zero q hq),
      Ne.symm hx0,Ne.symm hx20,Ne.symm hxq,Ne.symm hx2q,?_,rfl⟩
    intro he
    exact two_quarters_ne_zero q hq (add_left_cancel (by simpa using he.symm : x+2 • (q : ZMod (4*q))=x+0))







end Couret.InterIA.Catalogue.Quarter

theorem solution : ∀ (q : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
    ∀
      (x :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)),
      Iff
        (@Eq.{1} Nat
          (@Finset.card.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
            (Couret.InterIA.Catalogue.Quarter.patternA q x))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (Not
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
            (Couret.InterIA.Catalogue.Quarter.badParameters q) x)) := @_root_.Couret.InterIA.Catalogue.Quarter.p2m_local_patternA_card_iff

