-- Prove2me | solution 1 for lt_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:25.724169+00:00
-- url     : https://prove2.me/submissions/d7016cad-0bba-4ce4-b8b9-334388efbb17

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul



set_option autoImplicit false
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
theorem _root_.solution (p : Submodule R M) {p' : Submodule R p}
    (q : { q : Submodule R p // p' ≤ q} )
    (h : q ≠ ⊤) : Submodule.map p.subtype q.val < p := by
  apply lt_of_le_of_ne
  · rw [Submodule.map_le_iff_le_comap]
    simp
  · intro hc
    absurd h
    rw [eq_top_iff]
    rintro x -
    simp
    have : x.val ∈ Submodule.map p.subtype q := by
      rw [hc]
      exact x.property
    simpa using this
