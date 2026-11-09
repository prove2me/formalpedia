-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_nonempty_of_card_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:48.608056+00:00
-- url     : https://prove2.me/submissions/1dd2bf4d-164e-4153-86ef-bf2e8b5e11eb

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
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

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]



















/-- There is at least one zero-free triple-square fibre in every group
having at least four elements, with no restriction on its torsion. -/
theorem p2m_local_zeroFreeFullFibres_nonempty_of_card_ge_four
    (hn : 4 ≤ Fintype.card G) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).Nonempty := by
  have hcard : ((Finset.univ : Finset G).erase (0 : G)).card =
      Fintype.card G - 1 := by simp
  have hle : 3 ≤ ((Finset.univ : Finset G).erase (0 : G)).card := by
    omega
  obtain ⟨S, hSsub, hS3⟩ := Finset.exists_subset_card_eq hle
  have hSno : (0 : G) ∉ S := by
    intro h0
    have h0' := hSsub h0
    exact (Finset.mem_erase.mp h0').1 rfl
  have hSF : S ∈ squareFibre S := (mem_squareFibre S S).mpr
    ⟨hS3, fun _ => rfl⟩
  have hNZ : S ∈ withoutZero (squareFibre S) :=
    Finset.mem_filter.mpr ⟨hSF, hSno⟩
  have hAll : squareFibre S ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
    Finset.mem_image.mpr ⟨S, (mem_tripleSupports S).mpr hS3, rfl⟩
  have hNon : squareFibre S ∈
      (nonemptyFullFibres : Finset (Finset (Finset G))) :=
    Finset.mem_filter.mpr ⟨hAll, ⟨S, hNZ⟩⟩
  exact ⟨withoutZero (squareFibre S), Finset.mem_image.mpr ⟨squareFibre S, hNon, rfl⟩⟩








end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Fintype.card.{p2m_u_0} G inst_2) →
    @Finset.Nonempty.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_nonempty_of_card_ge_four

