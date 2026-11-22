-- Prove2me | Definitions.Def_Kourovka_Modules_ValuationModule
-- name    : Kourovka_Modules_ValuationModule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:10.545882+00:00
-- url     : https://prove2.me/theorems/c9b5e1b5-c358-47a9-93b8-0fbd8a9a3103
-- title:
--   Valuation Module
-- statement:
--   Definitions and structural lemmas for Valuation Module, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
abbrev GroupRing (Q : Type*) [AddCommGroup Q] := AddMonoidAlgebra ℤ Q
def nonnegativeRing (χ : Q →+ ℝ) : Subring (GroupRing Q) where
  carrier := {p | ∀ u ∈ p.support, 0 ≤ χ u}
  zero_mem' := by
    intro u hu
    exact False.elim ((Finsupp.mem_support_iff.mp hu) rfl)
  one_mem' := by
    intro u hu
    have : u = 0 := by simpa [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply, eq_comm] using hu
    simp [this]
  add_mem' := by
    intro p q hp hq u hu
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · exact hp u hu
    · exact hq u hu
  neg_mem' := by
    intro p hp u hu
    exact hp u (by simpa using hu)
  mul_mem' := by
    intro p q hp hq u hu
    obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_image₂.mp (AddMonoidAlgebra.support_mul p q hu)
    simpa using add_nonneg (hp v hv) (hq w hw)
def positiveIdeal (χ : Q →+ ℝ) : Ideal (nonnegativeRing χ) where
  carrier := {p | ∀ u ∈ (p : GroupRing Q).support, 0 < χ u}
  zero_mem' := by
    intro u hu
    exact False.elim ((Finsupp.mem_support_iff.mp hu) rfl)
  add_mem' := by
    intro p q hp hq u hu
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · exact hp u hu
    · exact hq u hu
  smul_mem' := by
    intro p q hq u hu
    obtain ⟨v, hv, w, hw, rfl⟩ :=
      Finset.mem_image₂.mp (AddMonoidAlgebra.support_mul (p : GroupRing Q) q hu)
    simpa using add_pos_of_nonneg_of_pos (p.2 v hv) (hq w hw)
def positiveMonomial (χ : Q →+ ℝ) (q : Q) (hq : 0 < χ q) : nonnegativeRing χ :=
  ⟨AddMonoidAlgebra.single q 1, by
    intro u hu
    have : u = q := by simpa [AddMonoidAlgebra.single_apply, eq_comm] using hu
    exact this.symm ▸ hq.le⟩
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
def LowerBound (χ : Q →+ ℝ) (p : GroupRing Q) (c : ℝ) : Prop :=
  ∀ u ∈ p.support, c ≤ χ u
end Kourovka.MetabelianEnumeration.ValuationModule


