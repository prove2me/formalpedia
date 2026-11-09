-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_size_h_exists_of_no_three_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:26.797388+00:00
-- url     : https://prove2.me/submissions/f6b69f1a-67b5-4bb9-a22b-06cb0660c693

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_squareFibre
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareFibre_card_of_no_exception
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





















/-- If there is no nonzero three-torsion and three group elements lie
outside G[2], an ordinary zero-free fibre of size h actually exists. -/
theorem p2m_local_zeroFreeFullFibres_size_h_exists_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1)
    (hOutside : 3 ≤
      ((Finset.univ : Finset G) \ (twoTorsion : Finset G)).card) :
    ∃ R : Finset (Finset G),
      R ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) ∧
      R.card = (twoTorsion : Finset G).card := by
  obtain ⟨S, hSub, hS3⟩ :=
    Finset.exists_subset_card_eq hOutside
  have hIntersection : S ∩ (twoTorsion : Finset G) = ∅ := by
    ext x
    constructor
    · intro hx
      have hSX : x ∈ S := (Finset.mem_inter.mp hx).1
      have hHX : x ∈ (twoTorsion : Finset G) :=
        (Finset.mem_inter.mp hx).2
      exact False.elim ((Finset.mem_sdiff.mp (hSub hSX)).2 hHX)
    · intro hx
      simp at hx
  have hExceptionalZero :
      (exceptionalFibres : Finset (Finset (Finset G))) = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [exceptionalFibres_card_numeric]
    simp [ht]
  have hNoException : ∀ T : Finset G, ¬ ExceptionalPartner S T := by
    intro T hT
    have hES : S ∈ (exceptionalSupports : Finset (Finset G)) :=
      (mem_exceptionalSupports S).mpr ⟨hS3, ⟨T, hT⟩⟩
    have hEF : squareFibre S ∈
        (exceptionalFibres : Finset (Finset (Finset G))) :=
      Finset.mem_image.mpr ⟨S, hES, rfl⟩
    rw [hExceptionalZero] at hEF
    simpa using hEF
  have hSize : (withoutZero (squareFibre S)).card =
      (twoTorsion : Finset G).card := by
    rw [withoutZero_squareFibre,
      zeroFreeSquareFibre_card_of_no_exception S hS3 hNoException,
      hIntersection]
    simp
  have hPositive : (withoutZero (squareFibre S)).Nonempty := by
    apply Finset.card_pos.mp
    rw [hSize]
    exact twoTorsion_card_pos
  have hAll : squareFibre S ∈
      (allSquareFibres : Finset (Finset (Finset G))) :=
    Finset.mem_image.mpr ⟨S, (mem_tripleSupports S).mpr hS3, rfl⟩
  have hFull : squareFibre S ∈
      (nonemptyFullFibres : Finset (Finset (Finset G))) :=
    Finset.mem_filter.mpr ⟨hAll, hPositive⟩
  refine ⟨withoutZero (squareFibre S), ?_, hSize⟩
  exact Finset.mem_image.mpr ⟨squareFibre S, hFull, rfl⟩




















end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@Finset.card.{p2m_u_0} G
          (@SDiff.sdiff.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instSDiff.{p2m_u_0} G inst_1)
            (@Finset.univ.{p2m_u_0} G inst_2) (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) →
      @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun R =>
        And
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
              (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
            (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) R)
          (@Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_size_h_exists_of_no_three_torsion

