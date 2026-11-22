-- Prove2me | solution 1 for ideal_smul_lt_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:28.453084+00:00
-- url     : https://prove2.me/submissions/cf0df9f8-6d6a-4efc-88a4-40cd1cac214c

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Submodule_quotient_equiv_eq_bot_iff
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul

set_option autoImplicit false
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
theorem _root_.solution {I : Ideal R} (p : Submodule R M)
    (q : { q : Submodule R p // (I • ⊤ : Submodule R p) ≤ q} ) (h : q ≠ ⊥) :
    I • p < Submodule.map p.subtype q.val := by
  apply lt_of_le_of_ne
  · intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n hn
      let n' : p := ⟨n, hn⟩
      have : r • n' ∈ q.val := by
        apply q.property
        exact Submodule.smul_mem_smul hr trivial
      use r • n', this
      rfl
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  · intro hc
    apply_fun Submodule.comap p.subtype at hc
    rw [Submodule.comap_map_eq_self] at hc
    simp at hc
    absurd h
    rw [Submodule.quotient_equiv_eq_bot_iff]
    exact hc.symm
    simp
