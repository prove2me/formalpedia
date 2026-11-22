-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceSplitting.left_eq_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:51.736276+00:00
-- url     : https://prove2.me/submissions/5efebb2c-ac7a-47ce-ba90-ddc3edb07743

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]
namespace Kourovka.MetabelianEnumeration.HalfspaceSplitting
theorem _root_.solution (C : Subgroup N) {c : N} (hc : c ∈ C) : left C c = right C c := by
  have h := HNNExtension.equiv_symm_eq_conj (φ := MulEquiv.refl C) (⟨c, hc⟩ : C)
  simpa [left, right, MulAut.conj_apply] using h
end Kourovka.MetabelianEnumeration.HalfspaceSplitting
