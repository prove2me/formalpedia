-- Prove2me | solution 1 for Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_pos_of_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:40.131457+00:00
-- url     : https://prove2.me/submissions/e9aea4f3-b5bb-4348-a935-efff9fec622c

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]














/-- Four group elements suffice to choose three nonzero vertices, giving
a nonempty observed zero-free ordered-square fibre. -/
theorem p2m_local_maxObservedZeroFreeFibreSize_pos_of_four
    (hn : 4 ≤ Fintype.card G) :
    0 < maxObservedZeroFreeFibreSize (G := G) := by
  have hz : (0 : G) ∈ (Finset.univ : Finset G) := Finset.mem_univ _
  have hc : ((Finset.univ : Finset G).erase (0 : G)).card =
      Fintype.card G - 1 := by
    rw [Finset.card_erase_of_mem hz]
    simp
  have h3 : 3 ≤ ((Finset.univ : Finset G).erase (0 : G)).card := by
    omega
  obtain ⟨S, hsub, hS3⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset G).erase (0 : G)) h3
  have hNoZero : (0 : G) ∉ S := by
    intro h0
    have he : (0 : G) ∈ (Finset.univ : Finset G).erase (0 : G) := hsub h0
    simp at he
  have hSelf : S ∈ squareFibre S :=
    (mem_squareFibre S S).mpr ⟨hS3, fun _ => rfl⟩
  have hRestr : (withoutZero (squareFibre S)).Nonempty :=
    ⟨S, Finset.mem_filter.mpr ⟨hSelf, hNoZero⟩⟩
  have hAll : squareFibre S ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
    Finset.mem_image.mpr ⟨S, (mem_tripleSupports S).mpr hS3, rfl⟩
  have hFull : squareFibre S ∈
      (nonemptyFullFibres : Finset (Finset (Finset G))) :=
    Finset.mem_filter.mpr ⟨hAll, hRestr⟩
  have hObserved : withoutZero (squareFibre S) ∈
      (zeroFreeFullFibres : Finset (Finset (Finset G))) :=
    Finset.mem_image.mpr ⟨squareFibre S, hFull, rfl⟩
  have hSize : 0 < (withoutZero (squareFibre S)).card :=
    Finset.card_pos.mpr hRestr
  have hLe : (withoutZero (squareFibre S)).card ≤
      maxObservedZeroFreeFibreSize (G := G) := by
    unfold maxObservedZeroFreeFibreSize
    exact Finset.le_sup hObserved
  omega



























end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Fintype.card.{p2m_u_0} G inst_2) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Couret.STROBO2TORS.maxObservedZeroFreeFibreSize.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_maxObservedZeroFreeFibreSize_pos_of_four

