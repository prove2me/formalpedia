-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.admissible_patterns_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:34.345591+00:00
-- url     : https://prove2.me/submissions/9da56e84-5ade-4075-bf37-accc8caa2458

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_pair_separations
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_shift_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_as_shifted_A
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_quarter_ne_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_two_quarters_ne_zero
import Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_actual_square_iff
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo

theorem admissible_common_disjoint (q : ℕ) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    Disjoint ({0,(q : ZMod (4*q))} : Finset (ZMod (4*q))) (Couret.InterIA.Fibres.fibre (2 • (q : ZMod (4*q))) x) := by
  obtain ⟨hx0,hxq,hx20,hx2q⟩ := admissible_pair_separations q x hx
  apply Finset.disjoint_left.mpr
  intro z hc hf
  simp only [mem_insert,mem_singleton] at hc
  simp only [Couret.InterIA.Fibres.fibre,mem_insert,mem_singleton] at hf
  rcases hc with rfl|rfl <;> rcases hf with hf|hf
  · exact hx0 hf.symm
  · exact hx20 hf.symm
  · exact hxq hf.symm
  · exact hx2q hf.symm

theorem patternA_union_fibre (q : ℕ) (x : ZMod (4*q)) :
    patternA q x=({0,(q : ZMod (4*q))} : Finset (ZMod (4*q))) ∪ Couret.InterIA.Fibres.fibre (2 • (q : ZMod (4*q))) x := by
  ext z
  simp only [patternA,Couret.InterIA.Fibres.fibre,mem_insert,mem_singleton,mem_union]
  tauto

theorem patternB_union_fibre (q : ℕ) (x : ZMod (4*q)) :
    patternB q x=({0,(q : ZMod (4*q))} : Finset (ZMod (4*q))) ∪ Couret.InterIA.Fibres.fibre (2 • (q : ZMod (4*q))) (x+q) := by
  rw [patternB_as_shifted_A,patternA_union_fibre]

theorem p2m_local_admissible_patterns_collision (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    ∀ z, orderedSquare (patternA q x) z=orderedSquare (patternB q x) z := by
  have h2 : (2 • (q : ZMod (4*q)))+2 • (q : ZMod (4*q))=0 := by
    calc _=4 • (q : ZMod (4*q)) := by abel
         _=0 := four_quarters_zero q
  rw [patternA_union_fibre,patternB_union_fibre]
  apply (pp_actual_square_iff {0,(q : ZMod (4*q))} (2 • (q : ZMod (4*q))) (two_quarters_ne_zero q hq) h2 x (x+q)
    (admissible_common_disjoint q x hx)
    (admissible_common_disjoint q (x+q) ((admissible_shift_iff q x).mpr hx))).mpr
  have hC : indicator ({0,(q : ZMod (4*q))} : Finset (ZMod (4*q)))=1+atom (q : ZMod (4*q)) := by
    rw [indicator_pair 0 (q : ZMod (4*q)) (Ne.symm (quarter_ne_zero q hq))]
    have hz : atom (0 : ZMod (4*q))=1 := by simp [atom,AddMonoidAlgebra.one_def]
    rw [hz]
  have hQQ : atom (q : ZMod (4*q))*atom (q : ZMod (4*q))=atom (2 • (q : ZMod (4*q))) := by
    rw [atom_mul,two_nsmul]
  have hXQ : atom (x+q)=atom x*atom (q : ZMod (4*q)) := (atom_mul x q).symm
  have hH := antipodal_monomial_square (2 • (q : ZMod (4*q))) h2
  change atom (2 • (q : ZMod (4*q)))*atom (2 • (q : ZMod (4*q)))=1 at hH
  rw [hC,hXQ]
  calc
    _=((1+atom (2 • (q : ZMod (4*q))))*(1-atom (2 • (q : ZMod (4*q)))))*atom x*(1+atom x) := by
      rw [← hQQ]
      ring
    _=0 := by rw [Couret.InterIA.L4.antipodal_cross _ hH]; simp



end Couret.InterIA.Catalogue.Quarter

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
          (z :
            ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)),
          @Eq.{1} Nat
            (@Couret.InterIA.Parity.orderedSquare.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Ring.toAddCommGroup.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                (@CommRing.toRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                  (ZMod.commRing
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))
              (ZMod.decidableEq
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (Couret.InterIA.Catalogue.Quarter.patternA q x) z)
            (@Couret.InterIA.Parity.orderedSquare.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Ring.toAddCommGroup.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                (@CommRing.toRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                  (ZMod.commRing
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))
              (ZMod.decidableEq
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (Couret.InterIA.Catalogue.Quarter.patternB q x) z) := @_root_.Couret.InterIA.Catalogue.Quarter.p2m_local_admissible_patterns_collision

