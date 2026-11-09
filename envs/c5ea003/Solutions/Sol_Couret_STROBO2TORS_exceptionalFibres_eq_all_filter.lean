-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalFibres_eq_all_filter
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:22.674599+00:00
-- url     : https://prove2.me/submissions/1b93ed88-5d52-414b-8eba-e63ee84c6408

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]











































































theorem p2m_local_exceptionalFibres_eq_all_filter :
    (exceptionalFibres : Finset (Finset (Finset G))) =
      allSquareFibres.filter (fun F => F.card = 2 * (twoTorsion : Finset G).card) := by
  ext F
  constructor
  · intro hF
    obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
    obtain ⟨hs3, hcS⟩ := (mem_exceptionalSupports_card S).mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨S,
      (mem_tripleSupports S).mpr hs3, hsF⟩, by rw [← hsF]; exact hcS⟩
  · intro hF
    obtain ⟨hF, hcF⟩ := Finset.mem_filter.mp hF
    obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
    exact Finset.mem_image.mpr ⟨S, (mem_exceptionalSupports_card S).mpr
      ⟨(mem_tripleSupports S).mp hS, by rw [hsF]; exact hcF⟩, hsF⟩













end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)
    (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (fun F =>
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
      (fun a =>
        instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
      (@Couret.STROBO2TORS.allSquareFibres.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalFibres_eq_all_filter

